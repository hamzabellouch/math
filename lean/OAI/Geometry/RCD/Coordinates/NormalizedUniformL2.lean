import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! # Uniform almost-everywhere convergence gives normalized L2 convergence

The measures may vary and their masses need not be bounded away from zero.
Only positivity and finiteness of each normalizing mass are used.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalized_sq_mean_tendsto_zero (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (hmass : ∀ k, 0<(μ k).real univ)
    (f : ℕ → X → ℝ) (hf : ∀ k, AEStronglyMeasurable (f k) (μ k))
    (hlim : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |f k x|≤η) :
    Tendsto (fun k => ((μ k).real univ)⁻¹*(∫ x, (f k x)^2 ∂μ k)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun k => ha.trans_le (mul_nonneg
      (inv_nonneg.mpr (hmass k).le) (integral_nonneg fun _ => sq_nonneg _))
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
    have hbound := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (hmass k).le)
    rw [← mul_assoc,inv_mul_cancel₀ (hmass k).ne',one_mul,hηsq] at hbound
    linarith

end RegularPointCoordinates

end

end OAI
