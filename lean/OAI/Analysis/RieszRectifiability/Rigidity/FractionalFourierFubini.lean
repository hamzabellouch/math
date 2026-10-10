import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalRadialSymbol
import OAI.Analysis.RieszRectifiability.Rigidity.FourierPhaseDifference
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzFirstMomentTails

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter Function

def fractionalFourierKernel (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (q : Ambient (p + 1) × Ambient (p + 1)) : ℂ :=
  fractionalSymbolKernel (p + 1) q.1 q.2 • (fourierPhase q.1 x * g q.1)

theorem fractionalFourierKernel_norm (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (q : Ambient (p + 1) × Ambient (p + 1)) :
    ‖fractionalFourierKernel p g x q‖ = fractionalSymbolKernel (p + 1) q.1 q.2 * ‖g q.1‖ := by
  unfold fractionalFourierKernel
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (fractionalSymbolKernel_nonneg _ _ _),
    norm_mul, fourierPhase_norm, one_mul]

theorem fractionalFourierKernel_measurable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) : Measurable (fractionalFourierKernel p g x) := by
  unfold fractionalFourierKernel fractionalSymbolKernel inverseDistancePow fourierPhase
  simp_rw [Complex.real_smul]
  fun_prop

theorem fractionalFourierKernel_integrable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    Integrable (fractionalFourierKernel p g x)
      ((volume : Measure (Ambient (p + 1))).prod volume) := by
  obtain ⟨c, _, hc⟩ := fractionalSymbol_eq_positive_constant_mul_norm p
  apply (integrable_prod_iff (fractionalFourierKernel_measurable p g x).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun ξ =>
      (fractionalSymbolKernel_integrable p ξ).smul_const (fourierPhase ξ x * g ξ)
  · have heq : (fun ξ => ∫ h, ‖fractionalFourierKernel p g x (ξ, h)‖) =
        fun ξ => c * (‖ξ‖ * ‖g ξ‖) := by
      funext ξ
      simp_rw [fractionalFourierKernel_norm]
      rw [integral_mul_const]
      change fractionalSymbol p ξ * ‖g ξ‖ = _
      rw [hc ξ, mul_assoc]
    rw [heq]
    exact (schwartz_first_absolute_moment_integrable g).const_mul c

theorem fractionalFourierKernel_integral_section (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x ξ : Ambient (p + 1)) :
    (∫ h, fractionalFourierKernel p g x (ξ, h)) =
      fractionalSymbol p ξ • (fourierPhase ξ x * g ξ) :=
  integral_smul_const (fractionalSymbolKernel (p + 1) ξ) (fourierPhase ξ x * g ξ)

theorem fractionalFourierKernel_integral_swap (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    (∫ h, ∫ ξ, fractionalFourierKernel p g x (ξ, h)) =
      ∫ ξ, fractionalSymbol p ξ • (fourierPhase ξ x * g ξ) := by
  have hi := fractionalFourierKernel_integrable p g x
  calc
    _ = ∫ q, fractionalFourierKernel p g x q ∂(volume : Measure (Ambient (p + 1))).prod volume :=
      (integral_prod_symm (fractionalFourierKernel p g x) hi).symm
    _ = ∫ ξ, ∫ h, fractionalFourierKernel p g x (ξ, h) := integral_prod _ hi
    _ = _ := integral_congr_ae (Eventually.of_forall (fractionalFourierKernel_integral_section p g x))

end

end RieszRectifiability

end OAI
