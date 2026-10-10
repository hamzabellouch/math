import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalUniversalLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrderedPowerWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrderedProductSums
import Mathlib.Tactic.NormNum

namespace OAI

/-! # Coefficients in a product of exponentials of distinct free letters -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

local instance (n : ℕ) : DecidableEq (FreeMonoid (Fin n)) := Classical.decEq _

theorem rationalWordExponential_sum (c n : ℕ) (i : Fin n) :
    rationalWordExponential c n i =
      ∑ j : Fin (c + 1), MonoidAlgebra.single (FreeMonoid.of i ^ j.val)
        ((j.val.factorial : ℚ)⁻¹) := by
  rw [rationalWordExponential, Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [PowerSeries.coeff_exp, rationalWordLetter, MonoidAlgebra.single_pow]

theorem ordered_single_product {M : Type*} [Monoid M] {n : ℕ}
    (w : Fin n → M) (q : Fin n → ℚ) :
    (List.ofFn (fun i => MonoidAlgebra.single (w i) (q i))).prod =
      MonoidAlgebra.single (List.ofFn w).prod (∏ i, q i) := by
  induction n with
  | zero => simp [MonoidAlgebra.one_def]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, MonoidAlgebra.single_mul_single,
      Fin.prod_univ_succ]

theorem rationalExponentialProduct_sum (c n : ℕ) :
    rationalExponentialProduct c n =
      ∑ k : Fin n → Fin (c + 1),
        MonoidAlgebra.single (orderedPowerWord id (fun i => (k i).val))
          (∏ i, ((k i).val.factorial : ℚ)⁻¹) := by
  change (List.ofFn (fun i => rationalWordExponential c n i)).prod = _
  simp only [rationalWordExponential_sum]
  rw [ordered_product_sums]
  apply Finset.sum_congr rfl
  intro k _
  exact ordered_single_product _ _

theorem bounded_orderedPowerWord_injective (c n : ℕ) :
    Function.Injective (fun k : Fin n → Fin (c + 1) =>
      orderedPowerWord id (fun i => (k i).val)) := by
  intro k l h
  have he := orderedPowerWord_injective id Function.injective_id h
  funext i
  exact Fin.ext (congrFun he i)

theorem rationalExponentialProduct_coeff (c n : ℕ) (w : FreeMonoid (Fin n)) :
    (rationalExponentialProduct c n).coeff w =
      ∑ k : Fin n → Fin (c + 1),
        if orderedPowerWord id (fun i => (k i).val) = w
        then ∏ i, ((k i).val.factorial : ℚ)⁻¹ else 0 := by
  rw [rationalExponentialProduct_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]

theorem rationalExponentialProduct_ordered_coeff (c n : ℕ) (k : Fin n → Fin (c + 1)) :
    (rationalExponentialProduct c n).coeff (orderedPowerWord id (fun i => (k i).val)) =
      ∏ i, ((k i).val.factorial : ℚ)⁻¹ := by
  rw [rationalExponentialProduct_coeff]
  simp only [(bounded_orderedPowerWord_injective c n).eq_iff]
  simp

theorem rationalExponentialProduct_empty_coeff (c n : ℕ) :
    (rationalExponentialProduct c n).coeff 1 = 1 := by
  have h := rationalExponentialProduct_ordered_coeff c n (fun _ => 0)
  simpa [orderedPowerWord] using h

theorem rationalExponentialProduct_coefficient_bound (c n : ℕ) (w : FreeMonoid (Fin n)) :
    |(rationalExponentialProduct c n).coeff w| ≤ 1 := by
  by_cases hw : ∃ k : Fin n → Fin (c + 1), orderedPowerWord id (fun i => (k i).val) = w
  · obtain ⟨k, rfl⟩ := hw
    rw [rationalExponentialProduct_ordered_coeff, abs_of_nonneg]
    · calc
        _ ≤ ∏ _ : Fin n, (1 : ℚ) := Finset.prod_le_prod₀
          (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (fun i _ => by
            exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (k i).val))
        _ = 1 := by simp
    · exact Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [rationalExponentialProduct_coeff]
    have hz : (∑ k : Fin n → Fin (c + 1),
        if orderedPowerWord id (fun i => (k i).val) = w
        then ∏ i, ((k i).val.factorial : ℚ)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact ite_eq_right (fun h => hw ⟨k, h⟩)
    rw [hz, abs_zero]
    exact zero_le_one

end PolycyclicRecognition

end

end OAI
