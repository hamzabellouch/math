import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCharts
import OAI.Geometry.Relativity.CKS.LocalConstraints
import OAI.Geometry.Relativity.CKS.VolumeDefinitions
import OAI.Geometry.Relativity.CKS.BoundaryPartial

namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSBoundarySurface
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

omit [IsManifold I3 ∞ M] in
lemma ext_symm_lift [IsManifold I3 ∞ M] (x : M) (z : E2) :
    (extChartAt I3 x).symm (liftPlane z) = (chartAt H3 x).symm (liftHalf z) := by
  change (chartAt H3 x).symm (I3.symm (I3 (liftHalf z))) = _
  rw [I3.left_inv]
omit [IsManifold I3 ∞ M] in
lemma lift_mem_ext_target [IsManifold I3 ∞ M] (x : M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x).target) :
    liftPlane z ∈ (extChartAt I3 x).target := by
  change liftPlane z ∈ ((chartAt H3 x).extend I3).target
  rw [OpenPartialHomeomorph.extend_target']
  exact ⟨liftHalf z,hz,rfl⟩

lemma transition_lift_maps (x y : Boundary M) :
    MapsTo liftPlane ((boundaryChart x).symm ≫ₕ boundaryChart y).source
      ((extChartAt I3 x.val).symm ≫ extChartAt I3 y.val).source := by
  intro z hz
  change z ∈ (boundaryChart x).target ∧ (boundaryChart x).symm z ∈ (boundaryChart y).source at hz
  refine ⟨lift_mem_ext_target x.val hz.1, ?_⟩
  change (extChartAt I3 x.val).symm (liftPlane z) ∈ (extChartAt I3 y.val).source
  rw [ext_symm_lift]
  have h := hz.2
  change ((boundaryChart x).symm z).val ∈ (chartAt H3 y.val).source at h
  rw [boundaryChart_symm_val x hz.1] at h
  simpa only [extChartAt_source] using h

lemma transition_formula (x y : Boundary M) {z : E2}
    (hz : z ∈ ((boundaryChart x).symm ≫ₕ boundaryChart y).source) :
    ((boundaryChart x).symm ≫ₕ boundaryChart y) z =
      dropPlane (((extChartAt I3 x.val).symm ≫ extChartAt I3 y.val) (liftPlane z)) := by
  change dropPlane (I3 (chartAt H3 y.val ((boundaryChart x).symm z).val)) = _
  rw [boundaryChart_symm_val x hz.1]
  change _ = dropPlane (I3 (chartAt H3 y.val ((extChartAt I3 x.val).symm (liftPlane z))))
  rw [ext_symm_lift]

lemma inclusion_chart_formula (x : Boundary M) {z : E2}
    (hz : z ∈ (boundaryChart x).target) :
    writtenInExtChartAt I2 I3 x (Subtype.val : Boundary M → M) z = liftPlane z := by
  change I3 (chartAt H3 x.val (((boundaryChart x).symm z).val)) = _
  rw [boundaryChart_symm_val x hz, (chartAt H3 x.val).right_inv hz]
  rfl

lemma inclusion_chart_eventually (x : Boundary M) :
    writtenInExtChartAt I2 I3 x (Subtype.val : Boundary M → M) =ᶠ[𝓝 (extChartAt I2 x x)] liftPlane := by
  have ht : (boundaryChart x).target ∈ 𝓝 (extChartAt I2 x x) :=
    (boundaryChart x).open_target.mem_nhds ((boundaryChart x).map_source (mem_chart_source E2 x))
  filter_upwards [ht] with z hz
  exact inclusion_chart_formula x hz

lemma inclusion_smooth : ContMDiff I2 I3 ∞ (Subtype.val : Boundary M → M) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact ((liftPlane.contDiff.contDiffAt).congr_of_eventuallyEq (inclusion_chart_eventually x)).contDiffWithinAt

lemma inclusion_hasMFDeriv (x : Boundary M) :
    HasMFDerivAt I2 I3 (Subtype.val : Boundary M → M) x liftPlane := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact (liftPlane.hasFDerivAt.congr_of_eventuallyEq (inclusion_chart_eventually x)).hasFDerivWithinAt

lemma inclusion_mfderiv_injective (x : Boundary M) :
    Injective (mfderiv I2 I3 (Subtype.val : Boundary M → M) x) := by
  rw [(inclusion_hasMFDeriv x).mfderiv]
  intro a b h
  change liftPlane a = liftPlane b at h
  have hh : dropPlane (liftPlane a) = dropPlane (liftPlane b) := congrArg dropPlane h
  change (a : E2) = (b : E2)
  exact (drop_lift a).symm.trans (hh.trans (drop_lift b))

end CKSBoundarySurface

end

end OAI
