import Mathlib

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

abbrev Bits (b : ℕ) := Fin b → Bool

def hybrid {b : ℕ} (x y : Bits b) (k : ℕ) : Bits b :=
  fun i => if i.val < k then y i else x i

def TailEq {b : ℕ} (k : ℕ) (x y : Bits b) : Prop :=
  ∀ i : Fin b, k ≤ i.val → y i = x i

instance {b k : ℕ} (x y : Bits b) : Decidable (TailEq k x y) := by
  unfold TailEq
  infer_instance

lemma hybrid_update {b k : ℕ} (x y : Bits b) (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    hybrid x (Function.update y t v) k = hybrid x y k := by
  funext i
  unfold hybrid
  by_cases hi : i.val < k
  · rw [ite_eq_left hi, ite_eq_left hi, Function.update_of_ne]
    intro he; subst i; omega
  · rw [ite_eq_right hi, ite_eq_right hi]

lemma hybrid_of_tail {b k : ℕ} (x y : Bits b) (h : TailEq k x y) :
    hybrid x y k = y := by
  funext i
  unfold hybrid
  split_ifs with hi
  · rfl
  · exact (h i (by omega)).symm

lemma tail_update {b k : ℕ} (hk : k < b) (x y : Bits b) (v : Bool) :
    TailEq k x (Function.update y ⟨k,hk⟩ v) ↔
      v = x ⟨k,hk⟩ ∧ TailEq (k+1) x y := by
  constructor
  · intro h
    constructor
    · simpa using h ⟨k,hk⟩ le_rfl
    · intro i hi
      have hn : i ≠ (⟨k,hk⟩ : Fin b) := by intro he; have hh := congrArg Fin.val he; change i.val=k at hh; omega
      simpa only [Function.update_of_ne hn] using h i (by omega)
  · rintro ⟨hv,h⟩ i hi
    by_cases he : i.val = k
    · have hi' : i = (⟨k,hk⟩ : Fin b) := Fin.ext he
      subst i; simpa using hv
    · rw [Function.update_of_ne (by intro hh; exact he (congrArg Fin.val hh))]
      exact h i (by omega)

variable {A : Type*} [AddCommGroup A]

/-- Path translations for H on ascending physical wires followed by a
classically controlled translation on a separate additive register. -/
def pathShift {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) :
    (k : ℕ) → k ≤ b → A
  | 0, _ => 0
  | k+1, h => pathShift δ x y k (by omega) + δ ⟨k,by omega⟩ (hybrid x y (k+1))

noncomputable def hEntry (a c : Bool) : ℂ :=
  (if a && c then -1 else 1) / (Real.sqrt 2 : ℂ)

noncomputable def pathWeight {b : ℕ} (x y : Bits b) : (k : ℕ) → k ≤ b → ℂ
  | 0, _ => 1
  | k+1, h => pathWeight x y k (by omega) * hEntry (x ⟨k,by omega⟩) (y ⟨k,by omega⟩)

lemma pathShift_update {b k : ℕ} (hk : k ≤ b) (δ : Fin b → Bits b → A)
    (x y : Bits b) (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    pathShift δ x (Function.update y t v) k hk = pathShift δ x y k hk := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pathShift, pathShift, ih (by omega) (by omega), hybrid_update _ _ _ _ h]

lemma pathWeight_update {b k : ℕ} (hk : k ≤ b) (x y : Bits b)
    (t : Fin b) (v : Bool) (h : k ≤ t.val) :
    pathWeight x (Function.update y t v) k hk = pathWeight x y k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathWeight, pathWeight, ih (by omega) (by omega), Function.update_of_ne]
    intro he; have hh := congrArg Fin.val he; change k=t.val at hh; omega

/-- Exact pointwise action of the H/conditional-forward-translation sequence.
There is no projection or forced-success operation in this evolution. -/
noncomputable def evolve {b : ℕ} (δ : Fin b → Bits b → A) (x : Bits b) (χ : A → ℂ) :
    (k : ℕ) → k ≤ b → Bits b → A → ℂ
  | 0, _, y, z => if y = x then χ z else 0
  | k+1, h, y, z =>
    (evolve δ x χ k (by omega) (Function.update y ⟨k,by omega⟩ false)
      (z-δ ⟨k,by omega⟩ y) +
     (if y ⟨k,by omega⟩ then (-1:ℂ) else 1) *
     evolve δ x χ k (by omega) (Function.update y ⟨k,by omega⟩ true)
      (z-δ ⟨k,by omega⟩ y)) / (Real.sqrt 2 : ℂ)

/-- Every data wire has a single H and therefore exactly one compatible path
for each input/output pair, even though the phase register is coherent. -/
theorem evolve_path {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ)
    (k : ℕ) (hk : k ≤ b) (z : A) :
    evolve δ x χ k hk y z =
      if TailEq k x y then pathWeight x y k hk * χ (z-pathShift δ x y k hk) else 0 := by
  classical
  induction k generalizing y z with
  | zero =>
    have he : TailEq 0 x y ↔ y=x := by simp [TailEq, funext_iff]
    simp [evolve, pathWeight, pathShift, he]
  | succ k ih =>
    rw [evolve, ih _ (by omega), ih _ (by omega)]
    simp only [tail_update]
    rw [pathShift_update _ _ _ _ _ _ le_rfl,
      pathShift_update _ _ _ _ _ _ le_rfl,
      pathWeight_update _ _ _ _ _ le_rfl, pathWeight_update _ _ _ _ _ le_rfl]
    by_cases ht : TailEq (k+1) x y
    · rw [ite_eq_left ht, pathShift, pathWeight, hybrid_of_tail _ _ ht]
      rw [show z-δ ⟨k,by omega⟩ y-pathShift δ x y k (by omega) =
        z-(pathShift δ x y k (by omega)+δ ⟨k,by omega⟩ y) by abel]
      cases hx : x ⟨k,by omega⟩ <;> cases hy : y ⟨k,by omega⟩ <;>
        simp [ht, hEntry] <;> ring
    · simp [ht]

lemma evolve_full {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) (χ : A → ℂ) (z : A) :
    evolve δ x χ b le_rfl y z =
      pathWeight x y b le_rfl * χ (z-pathShift δ x y b le_rfl) := by
  rw [evolve_path, ite_eq_left (by intro i hi; exact False.elim (Nat.not_le.mpr i.isLt hi))]

end ExactQuantumFactoring.Triangular


end

end OAI
