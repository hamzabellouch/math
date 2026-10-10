import OAI.Geometry.RCD.Heat.KernelTwoTimeSlope

namespace OAI

/-! # The absolute two-time quadratic inequality for the actual kernel heat -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_two_time_abs_slope_bound
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {r σ s t : ℝ} (hσ : 0 < σ) (hr : 2*σ*(L:ℝ) < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    (hs : 0 < s) (ht : 0 < t) (x y : X) :
    |kernelHeat (hausdorff n X) hX.quadratic hk s f x-
      kernelHeat (hausdorff n X) hX.quadratic hk t f y| ≤
    σ/2*kernelHeat (hausdorff n X) hX.quadratic hk s H x+
      Real.exp (-K*(s+t))*(dist x y^2+2*N*(Real.sqrt s-Real.sqrt t)^2)/(2*σ) := by
  let μ := hausdorff n X
  have hp := hX.kernel_two_time_slope_bound K n hn hK hN hk hφ p R hsupp f H hf hσ hr hH hs ht x y
  have hfneg : (-φ) =ᵐ[μ] (-f : Lp ℝ 2 μ) := by
    filter_upwards [hf,Lp.coeFn_neg f] with z hz he
    simp only [he,Pi.neg_apply,hz]
  have hHneg : (fun z => (slopeAtScale (-φ) r z).toReal^2) =ᵐ[μ] H := by
    simpa only [slopeAtScale_neg_eq] using hH
  have hm := hX.kernel_two_time_slope_bound K n hn hK hN hk hφ.neg p R
    (fun z hz => by simp only [Pi.neg_apply,hsupp z hz,neg_zero]) (-f) H hfneg hσ hr hHneg hs ht x y
  simp only [kernelHeat,inner_neg_right] at hm
  apply abs_le.mpr
  exact ⟨by dsimp only [kernelHeat]; linarith only [hm],hp⟩

end RegularPointCoordinates

end

end OAI
