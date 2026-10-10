import OAI.Geometry.RCD.Harmonic.LocalRadialDerivative
import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # The actual radial derivative errors in the common normalized L2 space -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The derivative's local energy estimate passes directly to normalized
L2, including the original volume denominator. -/
theorem normalized_radial_derivative_norm_sq (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f q : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) :
    ‖normalizeLocalL2 μ Ω hfin (localRadialDerivative μ hQ Ω f hf q)‖ ^ 2 ≤
      B * (μ.real Ω)⁻¹ * ∫ x in Ω, localGamma μ hQ q q x ∂μ := by
  rw [normalizeLocalL2_norm_sq, ← l2_norm_sq_eq_integral]
  have hh := mul_le_mul_of_nonneg_left (localRadialDerivative_norm_sq μ hQ Ω f q hf)
    (show 0 ≤ (μ.real Ω)⁻¹ by positivity)
  convert hh using 1; ring

/-- The squared L2 norm of the algebraic commutator is exactly the
integral controlled by the full Poisson mass estimate. -/
theorem local_radial_commutator_norm_sq (Ω : Set X)
    (f v u g h : SobolevSpace μ hQ) {Cf Cv : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ Cf)
    (hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ v v x ≤ Cv)
    (hh : SobolevSpace.toLp μ hQ h =ᵐ[μ.restrict Ω] localGamma μ hQ v u) :
    ‖localRadialDerivative μ hQ Ω v hv g - localRadialDerivative μ hQ Ω f hf h -
      SobolevSpace.restrictLp μ hQ Ω h‖ ^ 2 =
    ∫ x in Ω, (localGamma μ hQ v g x - localGamma μ hQ f h x - localGamma μ hQ v u x) ^ 2 ∂μ := by
  rw [l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [localRadialDerivative_representative μ hQ Ω v g hv,
    localRadialDerivative_representative μ hQ Ω f h hf,
    SobolevSpace.restrictLp_coe μ hQ Ω h, hh,
    Lp.coeFn_sub (localRadialDerivative μ hQ Ω v hv g) (localRadialDerivative μ hQ Ω f hf h),
    Lp.coeFn_sub (localRadialDerivative μ hQ Ω v hv g - localRadialDerivative μ hQ Ω f hf h)
      (SobolevSpace.restrictLp μ hQ Ω h)] with x hg hf' hr hh' hs ht
  simp only [ht, hs, Pi.sub_apply, hg, hf', hr, hh']

end RegularPointCoordinates

end

end OAI
