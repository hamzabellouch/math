import OAI.Geometry.NodalSets.Charts.ImmersionMetric
import OAI.Geometry.NodalSets.Charts.SphereChartVolume

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

abbrev SphereCotangent (x : Base) := TangentSpace (𝓡 4) x →L[ℝ] ℝ
abbrev CotangentModel := BaseModel →L[ℝ] ℝ

def sphereCovectorRestriction (x : Base) : AmbientBase →L[ℝ] SphereCotangent x :=
  ((sphereAmbientDerivative x).precomp ℝ).comp (innerSL ℝ)

lemma sphereCovectorRestriction_apply (x : Base) (v : AmbientBase)
    (u : TangentSpace (𝓡 4) x) :
    sphereCovectorRestriction x v u = ⟪v, sphereAmbientDerivative x u⟫ := rfl

lemma sphereCovectorRestriction_radial (x : Base) :
    sphereCovectorRestriction x (x : AmbientBase) = 0 := by
  ext u
  have h := sphere_derivative_radial_orthogonal x u
  simpa [sphereCovectorRestriction_apply, PiLp.inner_apply, dotProduct, mul_comm] using h

lemma sphereCovectorRestriction_separates (x : Base) (v : AmbientBase)
    (hv : sphereCovectorRestriction x v = 0) (hr : ⟪(x : AmbientBase),v⟫ = 0) : v = 0 := by
  have hm : v ∈ (ℝ ∙ (x : AmbientBase))ᗮ := by
    exact (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := AmbientBase)).mpr (by simpa only [real_inner_comm] using hr)
  rw [← range_mvfderiv_subtypeVal (n := 4)] at hm
  obtain ⟨u,hu⟩ := hm
  have h := congrArg (fun f : SphereCotangent x ↦ f u) hv
  change ⟪v,sphereAmbientDerivative x u⟫ = 0 at h
  change sphereAmbientDerivative x u = v at hu
  rw [hu, real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

lemma sphereCovectorRestriction_smooth (v : AmbientBase) :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel)) ∞
      (fun x ↦ TotalSpace.mk' CotangentModel
        (E := SphereCotangent) x (sphereCovectorRestriction x v)) := by
  let f : Base → ℝ := fun x ↦ ⟪v,(x : AmbientBase)⟫
  have hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f :=
    (innerSL ℝ v).contMDiff.comp (contMDiff_coe_sphere (n := 4))
  have he (x : Base) : mfderiv (𝓡 4) 𝓘(ℝ,ℝ) f x = sphereCovectorRestriction x v := by
    have h := mfderiv_comp x ((innerSL ℝ v).mdifferentiableAt)
      ((contMDiff_coe_sphere (n := 4) (m := ∞)).mdifferentiable (by simp) x)
    rw [mfderiv_eq_fderiv, (innerSL ℝ v).fderiv] at h
    exact h
  simpa only [he] using Yau.Geometry.smooth_ambient_derivative f hf

end
end Yau.Target

end OAI
