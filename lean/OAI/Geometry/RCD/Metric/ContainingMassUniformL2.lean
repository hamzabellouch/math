import OAI.Geometry.RCD.Coordinates.NormalizedUniformL2

namespace OAI

/-! # Uniform errors on an inner region with the original mass normalization -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem containing_mass_uniform_l2 (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (m : ℕ → ℝ) (hm : ∀ k, 0 < m k)
    (hμ : ∀ k, (μ k).real univ ≤ m k)
    (f : ℕ → X → ℝ) (hf : ∀ k, AEStronglyMeasurable (f k) (μ k))
    (hlim : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |f k x|≤η) :
    Tendsto (fun k => (m k)⁻¹*(∫ x, (f k x)^2 ∂μ k)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun k => ha.trans_le (mul_nonneg
      (inv_nonneg.mpr (hm k).le) (integral_nonneg fun _ => sq_nonneg _))
  · intro b hb
    let η := Real.sqrt (b/2)
    have hη : 0<η := Real.sqrt_pos.mpr (half_pos hb)
    have hηsq : η^2=b/2 := Real.sq_sqrt (half_pos hb).le
    filter_upwards [hlim η hη] with k hk
    have hsq : ∀ᵐ x ∂μ k, (f k x)^2≤η^2 := hk.mono fun x hx =>
      by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hi : Integrable (fun x => (f k x)^2) (μ k) :=
      (integrable_const (η^2)).mono' ((hf k).pow 2)
        (hsq.mono fun x hx => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f k x))] using hx)
    have hint := integral_mono_ae hi (integrable_const (η^2)) hsq
    rw [integral_const,smul_eq_mul] at hint
    have hint' := hint.trans (mul_le_mul_of_nonneg_right (hμ k) (sq_nonneg η))
    have hbound := mul_le_mul_of_nonneg_left hint' (inv_nonneg.mpr (hm k).le)
    rw [← mul_assoc,inv_mul_cancel₀ (hm k).ne',one_mul,hηsq] at hbound
    linarith

end RegularPointCoordinates

end

end OAI
