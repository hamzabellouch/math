import OAI.Geometry.RCD.Heat.KernelHeatSharpLipschitz

namespace OAI

/-! # Pointwise initial values of compact Lipschitz heat data -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_initial_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hf : φ =ᵐ[hausdorff n X] f)
    (M : ℝ) (hM : ∀ x, |φ x|≤M) (x : X) :
    Tendsto (fun k => kernelHeat (hausdorff n X) hX.quadratic hk (heatStep k) f x)
      atTop (𝓝 (φ x)) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let C : ℝ≥0 := L*⟨Real.exp |K|,(Real.exp_pos _).le⟩
  have hC : L≤C := by
    apply NNReal.coe_le_coe.mp
    change (L:ℝ)≤(L:ℝ)*Real.exp |K|
    exact le_mul_of_one_le_right L.coe_nonneg (Real.one_le_exp (abs_nonneg K))
  have hLip (k : ℕ) : LipschitzWith C (kernelHeat μ Q hk (heatStep k) f) := by
    apply (hX.kernel_heat_sharp_lipschitz hn hk f hφ hf M hM (heatStep_pos k)).weaken
    apply NNReal.coe_le_coe.mp
    change (L:ℝ)*Real.exp (-K*heatStep k)≤(L:ℝ)*Real.exp |K|
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    apply Real.exp_le_exp.mpr
    have ht1 : heatStep k≤1 := by
      exact pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    calc
      -K*heatStep k ≤ |K| * heatStep k := mul_le_mul_of_nonneg_right (neg_le_abs K) (heatStep_pos k).le
      _ ≤ |K| := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 (abs_nonneg K)
  have hconv : Tendsto (fun k => heatAt μ Q (heatStep k) f) atTop (𝓝 f) := by
    have hh := ((heatAt_continuous μ Q f).tendsto 0).comp heatStep_tendsto
    simpa only [Function.comp_apply,heatAt_zero,one_apply_eq_self] using! hh
  exact lipschitz_lp_pointwise_convergence μ (fun y r hr => (hX.fullSupport y r hr).ne')
    (fun k => heatAt μ Q (heatStep k) f) f (fun k => kernelHeat μ Q hk (heatStep k) f)
    φ C hLip (hφ.weaken hC) (fun k => (kernelHeat_represents_L2 μ Q hk (heatStep_pos k) f).symm)
    hf.symm hconv x

end RegularPointCoordinates

end

end OAI
