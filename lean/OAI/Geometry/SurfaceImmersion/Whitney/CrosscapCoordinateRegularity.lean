import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapChartTransition
import OAI.Geometry.SurfaceImmersion.Geometry.NormalDefectDomain

namespace OAI

/-! Nondegenerate direction zeros are retained in the actual full-arc
coordinates, at both singular endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

lemma crosscap_coordinate_direction_regularity (C : SurfaceCrosscapCoordinates f p)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (hp : p ∈ c.source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (hEq : φ =ᶠ[𝓝 (c p)] f ∘ c.symm)
    (hv : fderiv ℝ φ (c p) (![0,1] : Base) = 0) :
    Function.Bijective (fderiv ℝ (surfaceDirection φ true) (c p,0)) := by
  obtain ⟨g,hg,hgp,hgD,hgEq⟩ := crosscap_chart_transition C c hcs hci hp hEq
  have htD : C.target.MDifferentiable 𝓘(ℝ,Base × ℝ) 𝓘(ℝ,ProjectionTarget 3) :=
    ⟨C.target_smooth.contMDiff.contMDiffOn.mdifferentiableOn (by simp),
      C.target_inverse_smooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htbij : Function.Bijective (fderiv ℝ C.target 0) := by
    rw [← mfderiv_eq_fderiv]
    exact htD.mfderiv_bijective C.target_mem
  exact normal_form_direction_regularity hφ hg C.target_smooth (c p) hgp hgD htbij hgEq hv

variable {q : M} {A : CrosscapConnectingArc f p q}

lemma CrosscapCoordinateStrip.endpoint_direction_regular (S : CrosscapCoordinateStrip A) :
    Function.Bijective (fderiv ℝ (surfaceDirection S.model true) (![0,A.arc.start],0)) ∧
      Function.Bijective (fderiv ℝ (surfaceDirection S.model true) (![0,A.arc.finish],0)) := by
  have hpsource : p ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.source).mp
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hqsource : q ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.target).mp
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hpchart : S.chart p = ![0,A.arc.start] :=
    (congrArg S.chart A.source).symm.trans
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have hqchart : S.chart q = ![0,A.arc.finish] :=
    (congrArg S.chart A.target).symm.trans
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ S.domain := by
    intro t ht
    apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
    constructor <;> linarith [S.width_pos,ht.1,ht.2]
  have hpdom : S.chart p ∈ S.domain := by rw [hpchart]; exact haxis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hqdom : S.chart q ∈ S.domain := by rw [hqchart]; exact haxis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hpV : fderiv ℝ S.model (S.chart p) (![0,1] : Base) = 0 := by rw [hpchart]; exact S.left_vertical
  have hqV : fderiv ℝ S.model (S.chart q) (![0,1] : Base) = 0 := by rw [hqchart]; exact S.right_vertical
  constructor
  · simpa only [hpchart] using crosscap_coordinate_direction_regularity A.left S.chart
      S.chart_smooth S.inverse_smooth hpsource S.model_smooth
        (S.model_eq.eventuallyEq_of_mem (S.domain_open.mem_nhds hpdom)) hpV
  · simpa only [hqchart] using crosscap_coordinate_direction_regularity A.right S.chart
      S.chart_smooth S.inverse_smooth hqsource S.model_smooth
        (S.model_eq.eventuallyEq_of_mem (S.domain_open.mem_nhds hqdom)) hqV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
