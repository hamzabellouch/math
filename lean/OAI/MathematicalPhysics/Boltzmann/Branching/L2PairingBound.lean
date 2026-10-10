import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Squared integral pairings for the velocity multiplier estimate -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem L2_norm_sq_integral (a : Lp ℂ 2 μ) :
    ‖a‖^2 = ∫ x, ‖a x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def]
  rw [← integral_re (L2.integrable_inner a a)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [inner_self_eq_norm_sq_to_K,RCLike.re_ofReal_pow])

theorem L2_pairing_sq_le (a b : Lp ℂ 2 μ) :
    ‖∫ x, inner ℂ (a x) (b x) ∂μ‖^2 ≤
      (∫ x, ‖a x‖^2 ∂μ)*(∫ x, ‖b x‖^2 ∂μ) := by
  rw [← L2.inner_def,← L2_norm_sq_integral,← L2_norm_sq_integral,← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm a b) 2

end BoltzmannNonuniqueness.Published

end

end OAI
