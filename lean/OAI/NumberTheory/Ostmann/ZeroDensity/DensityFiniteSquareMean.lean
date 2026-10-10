import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteContinuity
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianSubset

namespace OAI

/-! # Mean square of an actual finite piece of the smoothed square -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T c : ℝ,
      1 ≤ T → 0 < c → c ≤ 1 → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * (densityKernelCost Q T c) ^ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
            ∑ n ∈ S,
              ‖densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c) n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_primitive_subset
  refine ⟨(∫ u : ℝ, densityHalfGaussian u) * C,
    mul_pos densityHalfGaussian_integral_pos hC, ?_⟩
  intro N Q hQ T c hT hc hc1 S hS F hF
  let a := densityVerticalCoeff (fun n : ℕ => (n.divisors.card : ℂ)) (1 / 2 + c)
  let G := ∫ u : ℝ, densityHalfGaussian u
  let K := densityKernelCost Q T c
  have hG : 0 ≤ G := densityHalfGaussian_integral_pos.le
  have hp (χ : PrimitiveComplexCharacter) :
      Integrable (fun t => ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2)
        (volume.restrict (Icc (-T) T)) := by
    let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    exact (density_gaussian_character_integrable S a χ.character T).integral_prod_left
  have hspos : ∀ n ∈ S, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp (hS hn)).1
  have hpoint (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2 ≤
        K ^ 2 * G * ∫ u : ℝ, densityHalfGaussian u *
          ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2 := by
    apply (densityFiniteSquare_energy χ S hspos c t hc hc1).trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun u => mul_nonneg (densityHalfGaussian_pos u).le (sq_nonneg _)))
    apply mul_le_mul_of_nonneg_right _ hG
    apply pow_le_pow_left₀ (by positivity)
    exact density_kernel_cost_bound Q hQ T c hT hc χ (hF χ hχ) t (abs_le.mpr ht)
  have hm : (∑ χ ∈ F, ∫ t in Icc (-T) T,
      ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
      K ^ 2 * G * (∑ χ ∈ F, ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact (((densityFiniteSquare_continuousOn χ S hspos T hT).norm).pow 2).integrableOn_Icc
    · exact (hp χ).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hpoint χ hχ t ht
  apply hm.trans
  have h := mul_le_mul_of_nonneg_left (hb N Q hQ T hT S hS a F hF)
    (mul_nonneg (sq_nonneg K) hG)
  convert h using 1
  ring

end Ostmann

end OAI
