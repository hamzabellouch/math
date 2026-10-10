import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormalInverseVecNorm

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem normal_family_inverse_extension (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ r > 0, ∃ e : OpenPartialHomeomorph ((E × (E →L[ℝ] E)) × E) ((E × (E →L[ℝ] E)) × E),
      (e : ((E × (E →L[ℝ] E)) × E) → ((E × (E →L[ℝ] E)) × E)) = normalFamilyTotal g ∧
      e.source = normalFamilySource g ∧ ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target ∧
      (∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : E) r, (q,x) ∈ e.source) ∧
      ∃ ψ : (E × (E →L[ℝ] E)) × E → E, ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
        ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : E) r,
          (fun y => (e.symm (q,y)).2) =ᶠ[𝓝 (normalJetMap q.1 q.2
            ((metricChristoffel g q.1).bilinearComp q.2 q.2) x)] (fun y => ψ (q,y)) := by
  obtain ⟨e,he,hs,hi⟩ := exists_normal_family_inverse g
  obtain ⟨r,hr,hR⟩ := compact_normal_family_radius g hK
  have hsub : metricFrameSet g K ×ˢ Metric.closedBall (0 : E) r ⊆ e.source := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    rw [hs]
    exact hR q hq x hx
  let L := e '' (metricFrameSet g K ×ˢ Metric.closedBall (0 : E) r)
  have hL : IsCompact L := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall 0 r)).image_of_continuousOn (e.continuousOn.mono hsub)
  have hLt : L ⊆ e.target := by
    rintro _ ⟨w,hw,rfl⟩
    exact e.map_source (hsub hw)
  obtain ⟨ψ,hψ,hEq⟩ := smooth_extension_near_compact hL e.open_target hLt hi.snd
  refine ⟨r,hr,e,he,hs,hi,(fun q hq x hx => hsub ⟨hq,hx⟩),ψ,hψ,?_⟩
  intro q hq x hx
  have hm : e (q,x) ∈ L := ⟨(q,x),⟨hq,hx⟩,rfl⟩
  have hEqx := hEq.filter_mono (nhds_le_nhdsSet hm)
  have ht : Tendsto (fun y : E => (q,y))
      (𝓝 (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
      (𝓝 (e (q,x))) := by
    rw [he]
    exact (continuous_const.prodMk continuous_id).continuousAt
  exact hEqx.comp_tendsto ht
end YauCounterexamples

end

end OAI
