import OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
import Mathlib.Data.Nat.Squarefree

namespace OAI

/-! Tuple weights in integer and product residue environments. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
  {P : α → Type*} [∀ i, Fintype (P i)]

/-- An arbitrary offset for every prime coordinate includes all product
residue environments. The integer environment has every offset equal to zero. -/
noncomputable def familyCenter (value : (i : α) → P i → ℕ)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (n : ℤ) : ℝ :=
  ∏ i, ((if (value i (x i) : ℤ) ∣ offset i (x i) + n then 1 else 0) - (value i (x i) : ℝ)⁻¹)

noncomputable def familyTuple (value : (i : α) → P i → ℕ) (x : (i : α) → P i) : ℕ :=
  ∏ i, value i (x i)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyCenter_abs (value : (i : α) → P i → ℕ)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (n : ℤ) :
    |familyCenter value offset x n| =
      ∏ i, centerMagnitude (value i (x i) : ℝ)⁻¹ (decide ((value i (x i) : ℤ) ∣ offset i (x i) + n)) := by
  simp [familyCenter, abs_prod, centerMagnitude]

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyCenter_abs_le_one (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (n : ℤ) :
    |familyCenter value offset x n| ≤ 1 := by
  rw [familyCenter_abs]
  apply prod_le_one₀
  · intro i _
    exact centerMagnitude_nonneg _ _
  · intro i _
    have hp : (1 : ℝ) ≤ value i (x i) := by exact_mod_cast (hprime i (x i)).one_lt.le
    exact centerMagnitude_le_one _ _ (by positivity) ((inv_le_one₀ (by positivity)).mpr hp)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyCenter_padding_periodic (value : (i : α) → P i → ℕ)
    (offset : (i : α) → P i → ℤ) (x : (i : α) → P i) (h q : ℕ) (n : ℤ) :
    familyCenter value offset x (n + (h * q * familyTuple value x : ℕ)) =
      familyCenter value offset x n := by
  unfold familyCenter
  apply prod_congr rfl
  intro i _
  have hdiv : value i (x i) ∣ h * q * familyTuple value x :=
    dvd_mul_of_dvd_right (dvd_prod_of_mem (fun i => value i (x i)) (mem_univ i)) (h * q)
  have hdivInt : (value i (x i) : ℤ) ∣ (h * q * familyTuple value x : ℕ) := by exact_mod_cast hdiv
  simp only [← add_assoc, dvd_add_left hdivInt]

/-- The exact degree estimate, uniform over all residue offsets. -/
theorem familyCenter_square_sum_le (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime)
    (offset : (i : α) → P i → ℤ) (n : ℤ) (W : ℝ)
    (hV : ∀ i, ∑ p, (value i p : ℝ)⁻¹ ≤ 2 * W)
    (hdegree : (∑ i, ∑ p : P i, if (value i p : ℤ) ∣ offset i p + n then (1 : ℝ) else 0) ≤
      6 * W * Fintype.card α) :
    (∑ x : (i : α) → P i, |familyCenter value offset x n| ^ 2) ≤
      (8 * W) ^ Fintype.card α := by
  simp only [familyCenter_abs]
  apply squared_center_products_le (fun i p => (value i p : ℝ)⁻¹)
    (fun i p => decide ((value i p : ℤ) ∣ offset i p + n)) W
  · intro i p
    positivity
  · intro i p
    have hp : (1 : ℝ) ≤ value i p := by exact_mod_cast (hprime i p).one_lt.le
    exact (inv_le_one₀ (by positivity)).mpr hp
  · exact hV
  · simpa using hdegree

omit [DecidableEq α] [∀ i, Fintype (P i)] in
lemma familyTuple_primeFactors (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime) (x : (i : α) → P i)
    (hinj : Function.Injective (fun i => value i (x i))) :
    (familyTuple value x).primeFactors = univ.image (fun i => value i (x i)) := by
  classical
  have hprod : (∏ p ∈ univ.image (fun i => value i (x i)), p) = familyTuple value x := by
    rw [prod_image]
    · rfl
    · exact fun i _ j _ hij => hinj hij
  rw [← hprod]
  apply Nat.primeFactors_prod
  intro p hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  exact hprime i (x i)

omit [DecidableEq α] [∀ i, Fintype (P i)] in
/-- With distinct selected primes, the integer family center is exactly the
paper's product over prime divisors of the numerical tuple. -/
lemma familyCenter_zero_eq_centeredTuple (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime) (x : (i : α) → P i)
    (hinj : Function.Injective (fun i => value i (x i))) (n : ℤ) :
    familyCenter value (fun _ _ => 0) x n = centeredTuple (familyTuple value x).primeFactors n := by
  classical
  rw [familyTuple_primeFactors value hprime x hinj, centeredTuple, prod_image]
  · simp only [familyCenter, zero_add]
  · exact fun i _ j _ hij => hinj hij

end TwoPointCorrelations

end OAI
