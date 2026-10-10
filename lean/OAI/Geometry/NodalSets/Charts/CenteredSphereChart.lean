import OAI.Geometry.NodalSets.Charts.ChartFrameSmooth
import OAI.Geometry.NodalSets.Elliptic.StereographicSecondDerivative

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

def centeredSphereIsometry (p : Base) : BaseModel →ₗᵢ[ℝ] AmbientBase :=
  (ℝ ∙ ((-p : Base) : AmbientBase))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 4 (ne_zero_of_mem_unit_sphere (-p))).repr.symm.toLinearIsometry

lemma centeredSphereIsometry_orthogonal (p : Base) (v : BaseModel) :
    ⟪(p : AmbientBase),centeredSphereIsometry p v⟫ = (0:ℝ) := by
  have h := ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm v).property
  have he := (Submodule.mem_orthogonal_singleton_iff_inner_left
    (𝕜 := ℝ) (E := AmbientBase)).mp h
  change ⟪(p : AmbientBase),
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm v : AmbientBase)⟫ = 0
  simpa [real_inner_comm] using he

lemma centeredSphereChart_target (p : Base) : (extChartAt (𝓡 4) p).target = Set.univ := by
  rw [extChartAt_target]
  change id ⁻¹' (stereographic' 4 (-p)).target ∩ Set.range (id : BaseModel → BaseModel) = Set.univ
  simp

lemma centeredSphereChart_inverse (p : Base) :
    ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) =
      stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p) := by
  funext y
  change ((stereographic' 4 (-p)).symm y : AmbientBase) = _
  rw [stereographic'_symm_apply]
  change _ = stereoInvFunAux (-(p : AmbientBase))
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm y : AmbientBase)
  simp only [stereoInvFunAux, smul_add, smul_smul]
  rfl

lemma centeredSphereChart_inverse_zero (p : Base) : (extChartAt (𝓡 4) p).symm 0 = p := by
  apply Subtype.ext
  have h := congrFun (centeredSphereChart_inverse p) 0
  simpa [stereoInvFunAux] using h

lemma centeredSphereChart_value (p : Base) : extChartAt (𝓡 4) p p = 0 := by
  have h := (extChartAt (𝓡 4) p).right_inv
    (show (0:BaseModel) ∈ (extChartAt (𝓡 4) p).target by rw [centeredSphereChart_target]; trivial)
  simpa only [centeredSphereChart_inverse_zero] using h

lemma centeredSphereChart_derivative (p : Base) :
    sphereChartDerivative p 0 = (centeredSphereIsometry p).toContinuousLinearMap := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ AmbientBase := IsBoundedSMul.continuousSMul
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]
  have hs : HasFDerivAt (stereoInvFunAux (-(p : AmbientBase)))
      (ContinuousLinearMap.id ℝ AmbientBase) ((centeredSphereIsometry p).toContinuousLinearMap 0) := by
    simpa using hasFDerivAt_stereoInvFunAux (-(p : AmbientBase))
  have h := hs.comp (0:BaseModel)
    (centeredSphereIsometry p).toContinuousLinearMap.hasFDerivAt
  simpa using h.fderiv

end
end Yau.Target

end OAI
