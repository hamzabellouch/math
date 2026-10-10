import OAI.Geometry.RCD.Heat.KernelHeatInitialLimit
import OAI.Geometry.RCD.Heat.KernelTwoTimeAbsoluteSlope

namespace OAI

/-! # Uniform two-time heat differences for compact Lipschitz tests -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_time_difference {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ) (hsupp : ∀ x, R<dist p x → φ x=0)
    (hf : φ =ᵐ[hausdorff n X] f)
    {σ s t : ℝ} (hσ : 0<σ) (hs : 0<s) (ht : 0<t) (x : X) :
    |kernelHeat (hausdorff n X) hX.quadratic hk s f x-
      kernelHeat (hausdorff n X) hX.quadratic hk t f x|≤
      σ/2*(L:ℝ)^2+Real.exp (-K*(s+t))*(2*(n:ℝ)*(Real.sqrt s-Real.sqrt t)^2)/(2*σ) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let r := 2*σ*(L:ℝ)+1
  have hr : 0≤r := by dsimp only [r]; positivity
  let hm := slopeAtScale_sq_memLp μ hφ p R hsupp hr
  let H := hm.toLp (fun x => (slopeAtScale φ r x).toReal^2)
  have hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[μ] H := hm.coeFn_toLp.symm
  have hHb : ∀ᵐ x ∂μ, |H x|≤(L^2:ℝ≥0) := by
    filter_upwards [hH] with x hx
    rw [← hx,abs_of_nonneg (sq_nonneg _)]
    have hb := ENNReal.toReal_mono ENNReal.coe_ne_top (slopeAtScale_le_lipschitz hφ r x)
    simp only [ENNReal.coe_toReal] at hb
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hb 2
  have hheat : kernelHeat μ Q hk s H x≤(L:ℝ)^2 :=
    (le_abs_self _).trans ((hX.kernelHeat_bounded_regularity hn p hk H (L^2) hHb s hs).2 x)
  have hh := hX.kernel_two_time_abs_slope_bound K n hn hK (le_refl (n:ℝ)) hk hφ p R hsupp f H hf
    hσ (show 2*σ*(L:ℝ)<r by dsimp only [r]; linarith) hH hs ht x x
  have hb := mul_le_mul_of_nonneg_left hheat (div_nonneg hσ.le (by norm_num : (0:ℝ)≤2))
  simp only [dist_self,zero_pow (by decide : 2≠0),zero_add] at hh
  exact hh.trans (add_le_add hb le_rfl)

end RegularPointCoordinates

end

end OAI
