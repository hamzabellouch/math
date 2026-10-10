import Mathlib
import OAI.Geometry.WeakMTW.Variations.GeneratingNeighborhood
import OAI.Geometry.WeakMTW.Variations.GeneratingFocalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def generatingHessian (x y : M) (ε : ℝ) (q : Model n × Model n) :
    ((Model n × Model n) × Model n) →L[ℝ] ((Model n × Model n) × Model n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ (generatingAction x y ε)) (q,(crossFlowCoordinates x y 1 q).1)

 theorem generatingHessian_smooth (x y : M) {ε : ℝ} {q : Model n × Model n}
    (hq : GeneratingChartAction x y ε q) : ContDiffAt ℝ ∞ (generatingHessian x y ε) q := by
  have hH := (hq.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact hH.comp q (contDiffAt_id.prodMk hq.flow_smooth.fst)

 theorem generatingHessian_focal (x y : M) {ε : ℝ} (hε : ε ≠ 0) {q : Model n × Model n}
    (hq : ∀ᶠ r in 𝓝 q, GeneratingChartAction x y ε r) {κ : Model n}
    (hker : fderiv ℝ (fun r => (crossFlowCoordinates x y 1 r).1) q (0,κ) = 0)
    (a b : Model n) :
    generatingHessian x y ε q ((0,κ),0) ((a,b),0) = -metric x q.1 κ a := by
  have h₀ := mem_of_mem_nhds hq
  have hg : ∀ᶠ r in 𝓝 q, ∀ a b : Model n,
      fderiv ℝ (generatingAction x y ε) (r,(crossFlowCoordinates x y 1 r).1) ((a,b),0) = -metric x r.1 r.2 a := by
    filter_upwards [hq] with r hr a b
    simpa only [map_zero,zero_sub] using generatingAction_gradient x y hε hr.1 hr.2.1 hr.2.2.2 (a,b) 0
  exact generating_focal_hessian
    (h₀.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (h₀.flow_smooth.fst.differentiableAt (by simp)) hker hg a b

 theorem generatingHessian_vertical_nonneg (x y : M) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    {q : Model n × Model n} (hq : GeneratingChartAction x y ε q)
    (hm : dist ((stateChart x).symm q).1 (geodesic ((stateChart x).symm q) 1) = ‖((stateChart x).symm q).2‖)
    (κ : Model n) : 0 ≤ generatingHessian x y ε q ((0,κ),0) ((0,κ),0) := by
  exact vertical_min_hessian_nonneg
    (hq.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (generating_vertical_minimum x y hε hε₁ hq hm) κ

 theorem generatingHessian_symmetric (x y : M) {ε : ℝ} {q : Model n × Model n}
    (hq : GeneratingChartAction x y ε q)
    (U V : (Model n × Model n) × Model n) :
    generatingHessian x y ε q U V = generatingHessian x y ε q V U :=
    ((hq.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).isSymmSndFDerivAt (by norm_num)).eq U V

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
