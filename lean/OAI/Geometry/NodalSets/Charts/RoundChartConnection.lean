import OAI.Geometry.NodalSets.Charts.CenteredSphereMetricLemmas
import OAI.Geometry.NodalSets.Charts.MetricConnectionFamilyLemmas
import OAI.Geometry.NodalSets.Elliptic.SmoothBilinearPullback

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

def ambientRoundBilinear : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ := innerSL ℝ

def roundChartMetric (p : Base) (y : BaseModel) : BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ :=
  bilinearPullback ambientRoundBilinear (sphereChartDerivative p y)

lemma roundChartMetric_apply (p : Base) (y u v : BaseModel) :
    roundChartMetric p y u v = ⟪sphereChartDerivative p y u,sphereChartDerivative p y v⟫ := rfl

lemma roundChartMetric_center (p : Base) :
    roundChartMetric p 0 = innerSL ℝ (E := BaseModel) := by
  ext u v
  rw [roundChartMetric_apply,centeredSphereChart_derivative]
  exact (centeredSphereIsometry p).inner_map_map u v

lemma roundChartMetric_smooth (p : Base) : ContDiff ℝ ∞ (roundChartMetric p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have h := sphereChartDerivative_smooth_at p (y := y) (by rw [centeredSphereChart_target]; trivial)
  have hpre : ContMDiffAt 𝓘(ℝ,BaseModel)
      𝓘(ℝ,(AmbientBase →L[ℝ] ℝ) →L[ℝ] (BaseModel →L[ℝ] ℝ)) ∞
      (fun z ↦ (sphereChartDerivative p z).precomp ℝ) y := h.contMDiffAt.clm_precomp
  have hpost : ContMDiffAt 𝓘(ℝ,BaseModel) 𝓘(ℝ,BaseModel →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun z ↦ ambientRoundBilinear.comp (sphereChartDerivative p z)) y :=
    contMDiffAt_const.clm_comp h.contMDiffAt
  exact contMDiffAt_iff_contDiffAt.mp (hpre.clm_comp hpost)

lemma roundChartMetric_derivative_zero (p : Base) : fderiv ℝ (roundChartMetric p) 0 = 0 := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  ext w u v
  have hg := ((roundChartMetric_smooth p).differentiable (by simp) 0).hasFDerivAt
  have he := (hg.clm_apply (hasFDerivAt_const u (0 : BaseModel))).clm_apply
    (hasFDerivAt_const v (0 : BaseModel))
  have hi := (centeredSphereChart_direction_hasFDerivAt p u).inner ℝ
    (centeredSphereChart_direction_hasFDerivAt p v)
  have hh := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L w) (he.fderiv.symm.trans hi.fderiv)
  simpa [centeredSphereChart_derivative,centeredSphereIsometry_orthogonal,
    real_inner_comm,inner_smul_left,inner_smul_right] using hh

lemma roundChartMetric_connection_zero (p : Base) :
    metricConnection (roundChartMetric p 0) (fderiv ℝ (roundChartMetric p) 0) = 0 := by
  rw [roundChartMetric_derivative_zero]
  have hz : christoffelCovector (0 : BaseModel →L[ℝ] BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ) = 0 := by
    ext u v w
    rw [christoffelCovector_apply]
    simp
  simp only [metricConnection,hz,ContinuousLinearMap.comp_zero]

lemma centeredSphereIsometry_exists (p : Base) (v : AmbientBase)
    (hv : ⟪(p : AmbientBase),v⟫ = (0:ℝ)) :
    ∃ w : BaseModel, centeredSphereIsometry p w = v := by
  have hm : v ∈ (ℝ ∙ ((-p : Base) : AmbientBase))ᗮ := by
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ)).mpr
    simpa [real_inner_comm] using hv
  refine ⟨(OrthonormalBasis.fromOrthogonalSpanSingleton 4
    (ne_zero_of_mem_unit_sphere (-p))).repr ⟨v,hm⟩,?_⟩
  exact congrArg (fun w : (ℝ ∙ ((-p : Base) : AmbientBase))ᗮ ↦ (w : AmbientBase))
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm_apply_apply ⟨v,hm⟩)

end
end Yau.Target

end OAI
