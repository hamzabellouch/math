import OAI.NumberTheory.TwoPointCorrelations.HalaszLocalWindow
import OAI.NumberTheory.TwoPointCorrelations.HalaszNearRenormalization

namespace OAI

/-! # Upper distance cost of the reciprocal-count soft masks -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical ComplexConjugate

/-- Softening finitely many prime values increases distance to the
constant-one function by at most their reciprocal mass. -/
theorem count_mask_distance_zero_le (F : ℕ → ℂ) (hF : OneBounded F)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ) :
    squaredDistance (mrtCountMaskedCoefficient F P u) (mrtArchimedeanTwist 0) N ≤
      squaredDistance F (mrtArchimedeanTwist 0) N + ∑ p ∈ P, 1/(p:ℝ) := by
  have hpoint (p : ℕ) (hp : p ∈ primesUpTo N) :
      (1-(mrtCountMaskedCoefficient F P u p * conj (mrtArchimedeanTwist 0 p)).re)/(p:ℝ) ≤
      (1-(F p * conj (mrtArchimedeanTwist 0 p)).re)/(p:ℝ) +
        (if p ∈ P then 1/(p:ℝ) else 0) := by
    have hprime := (mem_filter.mp hp).2
    simp only [mrtArchimedeanTwist, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      map_one, mul_one, mrtCountMaskedCoefficient, mrtCountMask_prime P hP u hprime]
    by_cases hpP : p ∈ P
    · simp only [hpP, ite_true, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      have hr := (Complex.re_le_norm (F p)).trans (hF p hprime.pos)
      have hm := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hr)
      nlinarith
    · simp only [hpP, ite_false, Complex.ofReal_one, mul_one, add_zero, le_refl]
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib] at hs
  change squaredDistance (mrtCountMaskedCoefficient F P u) (mrtArchimedeanTwist 0) N ≤
    squaredDistance F (mrtArchimedeanTwist 0) N + _ at hs
  apply hs.trans
  apply add_le_add le_rfl
  calc
    (∑ p ∈ primesUpTo N, if p ∈ P then 1/(p:ℝ) else 0) =
        ∑ p ∈ (primesUpTo N) ∩ P, 1/(p:ℝ) := by
      rw [sum_ite_mem]
    _ ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_le_sum_of_subset_of_nonneg inter_subset_right
      (fun p _ _ => by positivity)

end JointDickman

end OAI
