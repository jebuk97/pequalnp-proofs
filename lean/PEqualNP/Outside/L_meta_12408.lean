import Mathlib
import PEqualNP.Defs

namespace Encoder12408

open PEqualNP.CircuitLowerBounds

abbrev Mask := Finset (Fin 4)

structure State where
  keys : Finset ℕ
  tag : ℕ → Mask
  known : Finset Mask

def Good (S : State) : Prop := ∀ i ∈ S.keys, S.tag i ∈ S.known

def cost (S : State) : ℕ := S.keys.card + S.known.card

def reads (S : State) (x : List Bool) (b : Fin 4) : Prop :=
  ∃ i ∈ S.keys, x.getD i false = true ∧ b ∈ S.tag i

def put (S : State) (i : ℕ) (m : Mask) : State :=
  let a := if i ∈ S.keys then S.tag i ∪ m else m
  ⟨insert i S.keys, Function.update S.tag i a, insert a S.known⟩

theorem put_good {S : State} (hs : Good S) (i : ℕ) (m : Mask) : Good (put S i m) := by
  intro j hj
  change j ∈ insert i S.keys at hj
  rcases Finset.mem_insert.mp hj with rfl | old
  · simp [put]
  · by_cases h : j = i
    · subst j; simp [put]
    · simp only [put, Function.update_of_ne h]
      exact Finset.mem_insert_of_mem (hs j old)

theorem put_cost (S : State) (i : ℕ) {m : Mask} (hm : m ∈ S.known) :
    cost (put S i m) ≤ cost S + 1 := by
  by_cases h : i ∈ S.keys
  · simp only [cost, put, ite_eq_left h, Finset.insert_eq_of_mem h]
    have := Finset.card_insert_le (S.tag i ∪ m) S.known
    omega
  · simp [cost, put, h, Finset.insert_eq_of_mem hm, Nat.add_right_comm]

theorem put_reads (S : State) (i : ℕ) (m : Mask) (x : List Bool) (b : Fin 4) :
    reads (put S i m) x b ↔ reads S x b ∨ (x.getD i false = true ∧ b ∈ m) := by
  constructor
  · rintro ⟨j,hj,hx,hb⟩
    change j ∈ insert i S.keys at hj
    by_cases e : j = i
    · subst j
      by_cases h : i ∈ S.keys
      · simp only [put, Function.update_self, ite_eq_left h, Finset.mem_union] at hb
        exact hb.elim (fun a => Or.inl ⟨i,h,hx,a⟩) (fun a => Or.inr ⟨hx,a⟩)
      · exact Or.inr ⟨hx,by simpa [put,h] using hb⟩
    · exact Or.inl ⟨j,(Finset.mem_insert.mp hj).resolve_left e,hx,by simpa [put,e] using hb⟩
  · rintro (⟨j,hj,hx,hb⟩ | ⟨hx,hb⟩)
    · refine ⟨j,Finset.mem_insert_of_mem hj,hx,?_⟩
      by_cases e : j = i
      · subst j; simp [put,hj,hb]
      · simpa [put,e] using hb
    · exact ⟨i,Finset.mem_insert_self _ _,hx,by by_cases h : i ∈ S.keys <;> simp [put,h,hb]⟩

def drop (S : State) (i : ℕ) : State := ⟨S.keys.erase i,S.tag,S.known⟩

theorem drop_good {S : State} (hs : Good S) (i : ℕ) : Good (drop S i) :=
  fun j hj => hs j (Finset.mem_of_mem_erase hj)

def putMany (S : State) (l : List ℕ) (m : Mask) : State :=
  l.foldl (fun t i => put t i m) S

theorem putMany_spec (S : State) (l : List ℕ) {m : Mask} (hm : m ∈ S.known) (hs : Good S) :
    Good (putMany S l m) ∧ cost (putMany S l m) ≤ cost S + l.length ∧
    ∀ x b, reads (putMany S l m) x b ↔ reads S x b ∨
      (b ∈ m ∧ ∃ i ∈ l, x.getD i false = true) := by
  induction l generalizing S with
  | nil => simp [putMany, hs]
  | cons i l ih =>
    obtain ⟨good,bound,sem⟩ := ih (put S i m) (Finset.mem_insert_of_mem hm) (put_good hs i m)
    refine ⟨good,?_,?_⟩
    · change cost (putMany (put S i m) l m) ≤ _
      have := put_cost S i hm
      simp only [List.length_cons]
      omega
    · intro x b
      change reads (putMany (put S i m) l m) x b ↔ _
      rw [sem, put_reads]
      have split : (∃ j ∈ i :: l, x.getD j false = true) ↔
          (x.getD i false = true ∨ ∃ j ∈ l, x.getD j false = true) := by
        constructor
        · rintro ⟨j,hj,hv⟩
          rcases List.mem_cons.mp hj with rfl | h
          · exact Or.inl hv
          · exact Or.inr ⟨j,h,hv⟩
        · rintro (hv | ⟨j,hj,hv⟩)
          · exact ⟨i,by simp,hv⟩
          · exact ⟨j,List.mem_cons_of_mem _ hj,hv⟩
      rw [split]
      tauto


def advance (x : List Bool) (g : Gate) : List Bool :=
  x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

theorem read_other (x : List Bool) (y : Bool) {i : ℕ} (hi : i ≠ x.length) :
    (x ++ [y]).getD i false = x.getD i false := by
  by_cases h : i < x.length
  · simp [List.getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem split_reads (S : State) (x : List Bool) (y : Bool) (b : Fin 4) :
    reads S (x ++ [y]) b ↔ reads (drop S x.length) x b ∨
      (x.length ∈ S.keys ∧ b ∈ S.tag x.length ∧ y = true) := by
  constructor
  · rintro ⟨i,hi,hv,hb⟩
    by_cases e : i = x.length
    · subst i; exact Or.inr ⟨hi,hb,by simpa [List.getD] using hv⟩
    · exact Or.inl ⟨i,Finset.mem_erase.mpr ⟨e,hi⟩, (read_other x y e) ▸ hv,hb⟩
  · rintro (⟨i,hi,hv,hb⟩ | ⟨hi,hb,hy⟩)
    · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
      exact ⟨i,mem,by rwa [read_other x y ne],hb⟩
    · exact ⟨x.length,hi,by simpa [List.getD] using hy,hb⟩

theorem unstep (S : State) (hs : Good S) (n : ℕ) (g : Gate)
    (hg : g.op = GateOp.or ∧ g.inputs.length ≤ 2) :
    ∃ T : State, Good T ∧ cost T ≤ cost S + 1 ∧
      ∀ (x : List Bool), x.length = n → ∀ b, reads T x b ↔ reads S (advance x g) b := by
  by_cases active : n ∈ S.keys
  · let R := drop S n
    have hm : S.tag n ∈ R.known := hs n active
    obtain ⟨good,bound,sem⟩ := putMany_spec R g.inputs hm (drop_good hs n)
    refine ⟨putMany R g.inputs (S.tag n),good,?_,?_⟩
    · have count := Finset.card_erase_add_one active
      have arity := hg.2
      dsimp [cost,R,drop] at bound ⊢
      omega
    · intro x hx b
      rw [sem, advance, split_reads, hx]
      simp [R, active, hg.1, GateOp.eval, List.any_eq_true]
  · refine ⟨S,hs,by omega,?_⟩
    intro x hx b
    rw [advance, split_reads, hx]
    simp only [active,false_and,or_false]
    have eq : drop S n = S := by
      cases S with
      | mk keys tag known =>
        dsimp [drop] at *
        rw [Finset.erase_eq_of_notMem active]
    rw [eq]

theorem backwards (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (S : State) (hs : Good S) (n : ℕ) : ∃ T : State, Good T ∧
      cost T ≤ cost S + gs.length ∧ ∀ x : List Bool, x.length = n → ∀ b,
        reads T x b ↔ reads S (gs.foldl advance x) b := by
  induction gs generalizing n with
  | nil => exact ⟨S,hs,by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨R,gr,cr,sr⟩ := ih (fun t h => hg t (List.mem_cons_of_mem _ h)) (n+1)
    obtain ⟨T,gt,ct,st⟩ := unstep R gr n g (hg g (by simp))
    refine ⟨T,gt,?_,?_⟩
    · simp only [List.length_cons]; omega
    · intro x hx b
      exact (st x hx b).trans (sr (advance x g) (by simp [advance,hx]) b)

def target (w : Fin 4 → ℕ) (i : ℕ) : Mask := Finset.univ.filter (fun b => w b = i)

def start (w : Fin 4 → ℕ) : State :=
  ⟨Finset.univ.image w, target w, Finset.univ.image (fun b => target w (w b))⟩

theorem start_good (w : Fin 4 → ℕ) : Good (start w) := by
  intro i hi
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image_of_mem (fun b => target w (w b)) (Finset.mem_univ b)

theorem start_cost (w : Fin 4 → ℕ) : cost (start w) ≤ 8 := by
  have ha := Finset.card_image_le (s := Finset.univ) (f := w)
  have hb := Finset.card_image_le (s := Finset.univ) (f := fun b => target w (w b))
  simp only [Finset.card_univ,Fintype.card_fin] at ha hb
  dsimp [cost,start]; omega

theorem start_reads (w : Fin 4 → ℕ) (x : List Bool) (b : Fin 4) :
    reads (start w) x b ↔ x.getD (w b) false = true := by
  constructor
  · rintro ⟨i,_,h,hb⟩
    have e : w b = i := (Finset.mem_filter.mp hb).2
    rwa [e]
  · intro h
    exact ⟨w b, Finset.mem_image_of_mem _ (Finset.mem_univ b), h, by simp [start,target]⟩

def input (p : Fin 14) := List.ofFn (fun q : Fin 14 => decide (q = p))

theorem input_read (p : Fin 14) (i : ℕ) : (input p).getD i false = true ↔ i = p.val := by
  by_cases h : i < 14
  · rw [List.getD_eq_getElem _ _ (by simpa only [input,List.length_ofFn] using h)]
    simp only [input,List.getElem_ofFn,decide_eq_true_eq,Fin.ext_iff]
  · rw [List.getD_eq_default _ _ (by simp [input]; omega)]
    have := p.isLt
    simp; omega

def profile (p : Fin 14) : Mask := Finset.univ.filter (fun b => (p.val + 1).testBit b.val = true)

theorem occupied : ∀ p : Fin 14, (profile p).Nonempty := by decide

theorem distinct : ∀ p q : Fin 14, profile p = profile q → p = q := by decide

theorem end_cost (T : State) (ht : Good T)
    (sem : ∀ p b, reads T (input p) b ↔ b ∈ profile p) : 28 ≤ cost T := by
  have obs (p : Fin 14) (b : Fin 4) : reads T (input p) b ↔ p.val ∈ T.keys ∧ b ∈ T.tag p.val := by
    constructor
    · rintro ⟨i,hi,hx,hb⟩
      obtain rfl := (input_read p i).1 hx
      exact ⟨hi,hb⟩
    · rintro ⟨hi,hb⟩
      exact ⟨p.val,hi,(input_read p p.val).2 rfl,hb⟩
  have mem (p : Fin 14) : p.val ∈ T.keys := by
    obtain ⟨b,hb⟩ := occupied p
    exact ((obs p b).1 ((sem p b).2 hb)).1
  have eq (p : Fin 14) : T.tag p.val = profile p := by
    ext b
    have h := (obs p b).symm.trans (sem p b)
    simpa [mem p] using h
  let f (p : Fin 14) : T.keys := ⟨p.val,mem p⟩
  let g (p : Fin 14) : T.known := ⟨profile p,eq p ▸ ht _ (mem p)⟩
  have card₁ := Fintype.card_le_of_injective f (fun a b h => Fin.ext (congrArg Subtype.val h))
  have card₂ := Fintype.card_le_of_injective g (fun a b h => distinct a b (congrArg Subtype.val h))
  simp only [Fintype.card_fin,Fintype.card_coe] at card₁ card₂
  unfold cost; omega

end Encoder12408

theorem PEqualNP.Outside.L_meta_12408 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val)) := by
  rintro ⟨C,hg,hc,h⟩
  choose w hw using h
  obtain ⟨T,ht,ct,sem⟩ := Encoder12408.backwards C.gates hg (Encoder12408.start w) (Encoder12408.start_good w) 14
  have upper := Encoder12408.start_cost w
  have lower := Encoder12408.end_cost T ht (by
    intro p b
    rw [sem (Encoder12408.input p) (by simp [Encoder12408.input]), Encoder12408.start_reads]
    change ((C.wires (Encoder12408.input p)).getD (w b) false = true) ↔ _
    unfold Encoder12408.input
    rw [hw b p]
    simp [Encoder12408.profile])
  change C.gates.length ≤ 19 at hc
  omega
