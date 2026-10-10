import Mathlib
import OAI.Probability.SKBarriers.Scalar.TiltedQuadraticIBP

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinGaussian_tent_error {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (n : ℕ) (V g : S → ParameterSpace n → ℝ)
    (hV : ∀ s, BoundedDerivs (V s)) (hc : ∀ s, ContDiff ℝ 1 (g s))
    (hg : ∀ s, HasExpGrowth (g s)) (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s)))
    (a : Fin n → ℝ) (hinv : ∀ s, TranslationInvariant (g s) (coordinateVector n a))
    (ε : ℝ) (hb : ∀ s z, |g s z| ≤ 1)
    (h₁ : ∀ s z, |fderiv ℝ (V s) z (coordinateVector n a)| ≤ ε)
    (h₂ : ∀ s z, |fderiv ℝ (fderiv ℝ (V s)) z (coordinateVector n a) (coordinateVector n a)| ≤ ε) :
    |(∫ sz, (coordinateLinear n a sz.2)^2*g sz.1 sz.2 ∂spinGaussianLaw n V 0)-
      (∑ i, (a i)^2)*(∫ sz, g sz.1 sz.2 ∂spinGaussianLaw n V 0)| ≤ ε^2+ε := by
  let := spinGaussianLaw_probability n V hV
  rw [spinGaussian_quadratic_invariant n V g hV hc hg hdg a hinv,add_sub_cancel_left]
  have H := norm_integral_le_of_norm_le_const (μ := spinGaussianLaw n V 0)
    (f := fun sz : S × ParameterSpace n => g sz.1 sz.2*
      ((fderiv ℝ (V sz.1) sz.2 (coordinateVector n a))^2+
       fderiv ℝ (fderiv ℝ (V sz.1)) sz.2 (coordinateVector n a) (coordinateVector n a)))
    (C := ε^2+ε) (ae_of_all _ (fun sz => by
      rw [Real.norm_eq_abs,abs_mul]
      have he : |(fderiv ℝ (V sz.1) sz.2 (coordinateVector n a))^2+
          fderiv ℝ (fderiv ℝ (V sz.1)) sz.2 (coordinateVector n a) (coordinateVector n a)| ≤ ε^2+ε := by
        apply (abs_add_le _ _).trans
        apply add_le_add _ (h₂ sz.1 sz.2)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (h₁ sz.1 sz.2) 2
      exact (mul_le_mul (hb sz.1 sz.2) he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

end SK.Analytic

end
end

end

end OAI
