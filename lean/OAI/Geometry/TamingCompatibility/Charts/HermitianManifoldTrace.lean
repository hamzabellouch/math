import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffSupported

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ContinuousAlternatingMap RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
 [T2Space X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma pullback_ddc_scalarChartLift {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hfD : tsupport f ⊆ (extChartAt Model p).target)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) :
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p f)))
      (extChartAt Model p).symm y = extDeriv (ExteriorForms.dc (coordinateJ J p) f) y := by
  rw [pullback_ddc J (scalarChartLift_smooth p hf hc hfD) p hy]
  apply ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact scalarChartLift_apply_inverse p f hz

lemma manifold_cutoffLog_trace_lower {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain)
    (hy : ‖y-b‖ < R) (hφb : φ b = 1) (hφy : φ =ᶠ[𝓝 y] fun _ => 1) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*s^2*(‖v‖^2+‖W b v‖^2)/(s^2+‖y-b‖^2+‖W b (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p
        (HermitianRadial.translatedCutoffLog W R s b)))) (extChartAt Model p).symm y
          ![v,coordinateJ J p y v] := by
  dsimp only
  let W := hermitianCenterExtension J p D hφ hc hφD
  have hyD : y ∈ D.domain := hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith)
  rw [pullback_ddc_scalarChartLift J p
    (HermitianRadial.translatedCutoffLog_smooth W R hs b)
    (HermitianRadial.translatedCutoffLog_compact W hR s b)
    (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans D.domain_subset)
    (D.domain_subset hyD)]
  have hW := hermitianCenterExtension_eventually_eq J p D hφ hc hφD hφy
  rw [← ExteriorForms.extDeriv_dc_congr_germ hW Filter.EventuallyEq.rfl]
  rw [← hW.self_of_nhds]
  exact HermitianRadial.cutoffLog_trace_lower W hR hs b y v hy
    (hermitianCenterExtension_square J p D hφ hc hφD hφy.self_of_nhds)
    (hermitianCenterExtension_square J p D hφ hc hφD hφb)

lemma manifold_cutoffSqrt_trace_lower {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain)
    (hy : ‖y-b‖ < R) (hφb : φ b = 1) (hφy : φ =ᶠ[𝓝 y] fun _ => 1) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p
        (HermitianRadial.translatedCutoffSqrt W R s b)))) (extChartAt Model p).symm y
          ![v,coordinateJ J p y v] := by
  dsimp only
  let W := hermitianCenterExtension J p D hφ hc hφD
  have hyD : y ∈ D.domain := hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith)
  rw [pullback_ddc_scalarChartLift J p
    (HermitianRadial.translatedCutoffSqrt_smooth W R hs b)
    (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
    (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hball).trans D.domain_subset)
    (D.domain_subset hyD)]
  have hW := hermitianCenterExtension_eventually_eq J p D hφ hc hφD hφy
  rw [← ExteriorForms.extDeriv_dc_congr_germ hW Filter.EventuallyEq.rfl]
  rw [← hW.self_of_nhds]
  exact HermitianRadial.cutoffSqrt_trace_lower W hR hs b y v hy
    (hermitianCenterExtension_square J p D hφ hc hφD hφy.self_of_nhds)
    (hermitianCenterExtension_square J p D hφ hc hφD hφb)
end TamingCompatibility.GeometricChart

end

end OAI
