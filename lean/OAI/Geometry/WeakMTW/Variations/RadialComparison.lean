import Mathlib
import OAI.Geometry.WeakMTW.Variations.RadialSplitAction
import OAI.Geometry.WeakMTW.Variations.HessianLinear

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem radialSplitAction_cross (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (ξ : TangentSpace (model n) x) :
    HasDerivAt (fun r : ℝ => fderiv ℝ (radialSplitAction x a s t)
      (chartAt (Model n) x x,r•ξ) (tangentChartLinear x ξ,0)) (-inner ℝ ξ ξ / s) 0 := by
  have hsI := strict_radial_mem_injectivity ha hs.le (hst.trans ht)
  have htI := strict_radial_mem_injectivity ha (hs.trans hst).le ht
  have hF : ContDiffAt ℝ 2 (radialSplitAction x a s t) (chartAt (Model n) x x,0) :=
    (radialSplitAction_smooth x ha hs hst ht).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hevent : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ),
      s•a+r•ξ ∈ injectivityDomain x ∧
      DifferentiableAt ℝ (radialSplitAction x a s t) (chartAt (Model n) x x,r•ξ) := by
    have h₁ : Tendsto (fun r : ℝ => s•a+r•ξ) (𝓝 0) (𝓝 (s•a)) := by
      simpa only [zero_smul,add_zero] using
        (show Continuous (fun r : ℝ => s•a+r•ξ) from continuous_const.add (continuous_id.smul continuous_const)).continuousAt.tendsto (x := (0 : ℝ))
    have h₂ : Tendsto (fun r : ℝ => (chartAt (Model n) x x,r•ξ)) (𝓝 0) (𝓝 (chartAt (Model n) x x,0)) := by
      simpa only [zero_smul] using
        (show Continuous (fun r : ℝ => (chartAt (Model n) x x,r•ξ)) from continuous_const.prodMk (continuous_id.smul continuous_const)).continuousAt.tendsto (x := (0 : ℝ))
    filter_upwards [h₁ ((injectivityDomain_open x).mem_nhds hsI),
      h₂ ((hF.eventually (by norm_num)).mono (fun _ hh => hh.differentiableAt (by norm_num)))] with r hr₁ hr₂
    exact ⟨hr₁,hr₂⟩
  have heq : (fun r : ℝ => fderiv ℝ (radialSplitAction x a s t)
      (chartAt (Model n) x x,r•ξ) (tangentChartLinear x ξ,0)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => (-inner ℝ ξ ξ / s)*r) := by
    filter_upwards [hevent] with r hr
    rw [radialSplitAction_initial_derivative x a (r•ξ) s t hr.1 htI hr.2]
    simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
    have hmetric (u v : TangentSpace (model n) x) :
        metric x (chartAt (Model n) x x) (tangentChartLinear x u) (tangentChartLinear x v) = inner ℝ u v := by
      rw [tangentChartLinear_eq,tangentChartLinear_eq]
      exact stateChart_pairing x x (mem_chart_source (Model n) x) u v
    rw [hmetric a ξ,hmetric ξ ξ]
    field_simp [hs.ne',(hs.trans hst).ne']
    ring
  simpa only [mul_one] using (((hasDerivAt_id (0 : ℝ)).const_mul (-inner ℝ ξ ξ / s))).congr_of_eventuallyEq heq

 theorem radialSplitAction_hessian (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (ξ : TangentSpace (model n) x) :
    fderiv ℝ (fderiv ℝ (fun z => radialSplitAction x a s t (z,0)))
      (chartAt (Model n) x x) (tangentChartLinear x ξ) (tangentChartLinear x ξ) =
        actionHessian x (s•a) ξ ξ / s - actionHessian x (t•a) ξ ξ / t := by
  have hsI := strict_radial_mem_injectivity ha hs.le (hst.trans ht)
  have htI := strict_radial_mem_injectivity ha (hs.trans hst).le ht
  have hf : ContDiffAt ℝ 2 (initialCost x (exp x (s•a))) (chartAt (Model n) x x) :=
    (initialCost_geometry x hsI).1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiffAt ℝ 2 (initialCost x (exp x (t•a))) (chartAt (Model n) x x) :=
    (initialCost_geometry x htI).1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have heq : (fun z => radialSplitAction x a s t (z,0)) = (fun z =>
      initialCost x (exp x (s•a)) z / s + cost (exp x (s•a)) (exp x (t•a)) / (t-s) -
      initialCost x (exp x (t•a)) z / t) := by
    funext z
    simp only [radialSplitAction,add_zero,initialCost]
  rw [heq,DiscreteVariational.hessian_split hf hg]
  change _ = (fderiv ℝ (fderiv ℝ (initialCost x (exp x (s•a)))) (chartAt (Model n) x x)
    (tangentChartLinear x ξ) (tangentChartLinear x ξ) +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x (s•a))) / s -
    (fderiv ℝ (fderiv ℝ (initialCost x (exp x (t•a)))) (chartAt (Model n) x x)
    (tangentChartLinear x ξ) (tangentChartLinear x ξ) +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x (t•a))) / t
  simp only [map_smul,smul_eq_mul]
  field_simp [hs.ne',(hs.trans hst).ne']
  ring

 theorem radial_hessian_strict (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    {ξ : TangentSpace (model n) x} (hξ : ξ ≠ 0) :
    actionHessian x (s•a) ξ ξ / s > actionHessian x (t•a) ξ ξ / t := by
  have hf : ContDiffAt ℝ 2 (radialSplitAction x a s t) (chartAt (Model n) x x,0) :=
    (radialSplitAction_smooth x ha hs hst ht).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hcross := radialSplitAction_cross x ha hs hst ht ξ
  have hc : -inner ℝ ξ ξ / s ≠ 0 := div_ne_zero (neg_ne_zero.mpr (real_inner_self_pos.mpr hξ).ne') hs.ne'
  have hp := DiscreteVariational.horizontal_hessian_positive hf
    (radialSplitAction_min x ha hs hst ht) (tangentChartLinear x ξ) ξ hc
    (by simpa only [zero_add] using hcross)
  rw [radialSplitAction_hessian x ha hs hst ht ξ] at hp
  linarith

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
