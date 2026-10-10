import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedChartTwoSided
import OAI.Analysis.SymmetricDomains.OffsetDerivative

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma reconstruct_oldPosition (c : NashBoundaryChart (m := m) U V B q) (z : Affine m) :
    c.normal.realCoordinates.symm (c.oldParameter z,c.normal.graph (c.oldParameter z)+c.oldOffset z) = z := by
  rw [oldOffset,add_sub_cancel]
  exact c.normal.realCoordinates.symm_apply_apply z
end NashBoundaryChart
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

noncomputable def forward (s : NashBoundaryScalingChart c x)
    (z : Affine s.tangentDim × Affine s.normalDim) : Affine N :=
  c.chart.inverse (s.coordinates.symm z+c.oldPosition (c.normal.parameters x))

noncomputable def backward (s : NashBoundaryScalingChart c x) (y : Affine N) :
    Affine s.tangentDim × Affine s.normalDim :=
  s.coordinates (c.chart.projection (y-q c.center)-c.oldPosition (c.normal.parameters x))

def HasCutoffs (s : NashBoundaryScalingChart c x) : Prop :=
  ∀ z ∈ s.offsets.source,
    c.oldParameter (s.coordinates.symm z+c.oldPosition (c.normal.parameters x)) ∈ ball 0 c.graphRadius ∧
    ‖complexRealEquiv m (s.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < c.chart.radius ∧
    ‖c.oldOffset (s.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < 1

@[simp] theorem forward_zero (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.forward 0=q x := by
  simpa only [forward,map_zero,zero_add] using c.oldPosition_inverse hgood

@[simp] theorem backward_center (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.backward (q x)=0 := by
  simp only [backward,← c.oldPosition_projection hgood,sub_self,map_zero]

theorem backward_analytic (s : NashBoundaryScalingChart c x) : AnalyticOnNhd ℂ s.backward univ := by
  intro y _
  exact (s.coordinates.toContinuousLinearMap.analyticAt _).comp
    (((c.chart.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)).sub analyticAt_const)

theorem forward_analytic (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs) :
    AnalyticOnNhd ℂ s.forward s.offsets.source := by
  intro z hz
  exact (c.chart.inverse_analytic _ (hcut z hz).2.1).comp
    (f := fun z => s.coordinates.symm z+c.oldPosition (c.normal.parameters x)) (x := z)
    ((s.coordinates.symm.toContinuousLinearMap.analyticAt _).add analyticAt_const)

theorem backward_forward (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    s.backward (s.forward z)=z := by
  unfold backward forward
  rw [c.chart.left_inverse _ (hcut z hz).2.1,add_sub_cancel_right,s.coordinates.apply_symm_apply]

theorem forward_mem_variety (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    s.forward z ∈ V := c.chart.inverse_mem _ (hcut z hz).2.1

theorem family_iff (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    (s.offsets z).2 ∈ c.family (s.offsets z).1 ↔ s.forward z ∈ U := by
  rw [s.offsets_eq]
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  rw [c.reconstruct_oldPosition]
  exact ⟨fun h => h.2.2.2,fun h => ⟨(hcut z hz).1,(hcut z hz).2.2,(hcut z hz).2.1,h⟩⟩

noncomputable def domain (s : NashBoundaryScalingChart c x) (t : ℝ) :
    Set (Affine s.tangentDim × Affine s.normalDim) :=
  {z | weightedScale t z ∈ s.offsets.source ∧ s.forward (weightedScale t z) ∈ U}

theorem domain_eq (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs) (t : ℝ) :
    s.domain t = chartScaledDomain s.offsets c.family t := by
  ext z
  constructor
  · rintro ⟨hz,hu⟩
    exact ⟨hz,(s.family_iff hcut hz).mpr hu⟩
  · rintro ⟨hz,hu⟩
    exact ⟨hz,(s.family_iff hcut hz).mp hu⟩

theorem forward_backward_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y) :
    ∀ᶠ y in 𝓝[V] (q x), s.forward (s.backward y)=y := by
  have he := c.chart.right_inverse_at (a := c.oldPosition (c.normal.parameters x)) (c.graph_boundary _ hgood.2.1).2.1 F G
    (by simpa only [c.oldPosition_inverse hgood] using hF0) hF
    (by simpa only [c.oldPosition_inverse hgood] using hG) hGF
    (by simpa only [c.oldPosition_inverse hgood] using hFG)
  rw [c.oldPosition_inverse hgood] at he
  filter_upwards [he] with y hy
  simpa only [forward,backward,s.coordinates.symm_apply_apply,sub_add_cancel] using hy
end NashBoundaryScalingChart
end Release061

end

end OAI
