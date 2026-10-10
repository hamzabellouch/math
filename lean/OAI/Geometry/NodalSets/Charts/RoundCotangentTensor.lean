import OAI.Geometry.NodalSets.Charts.PositiveMetric
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundReference

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance roundCotangentTensorLocalInst1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
local instance roundCotangentTensorLocalInst2 (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedAddCommGroup BaseModel)
local instance roundCotangentTensorLocalInst3 (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedSpace ℝ BaseModel)
local instance roundCotangentTensorLocalInst4 (x : Base) : FiniteDimensional ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (FiniteDimensional ℝ BaseModel)

def sphereRoundForm (x : Base) : TangentSpace (𝓡 4) x →L[ℝ] TangentSpace (𝓡 4) x →L[ℝ] ℝ :=
  bilinearPullback (innerSL ℝ) (sphereAmbientDerivative x)

lemma sphereRoundForm_pos (x : Base) (v : TangentSpace (𝓡 4) x) (hv : v ≠ 0) :
    0 < sphereRoundForm x v v := by
  change 0 < ⟪sphereAmbientDerivative x v,sphereAmbientDerivative x v⟫
  apply real_inner_self_pos.mpr
  intro h
  exact hv ((injective_mvfderiv_subtypeVal_sphere (n := 4) x) (h.trans (map_zero _).symm))

def sphereRoundMusical (x : Base) : TangentSpace (𝓡 4) x ≃L[ℝ] SphereCotangent x :=
  positiveMetricEquiv (sphereRoundForm x) (sphereRoundForm_pos x)

def sphereCotangentRepresentative (x : Base) : SphereCotangent x →L[ℝ] AmbientBase :=
  (sphereAmbientDerivative x).comp (sphereRoundMusical x).symm.toContinuousLinearMap

lemma sphereCotangentRepresentative_pair (x : Base) (ell : SphereCotangent x)
    (v : TangentSpace (𝓡 4) x) :
    ⟪sphereCotangentRepresentative x ell,sphereAmbientDerivative x v⟫ = ell v := by
  exact congrArg (fun L : SphereCotangent x ↦ L v) ((sphereRoundMusical x).apply_symm_apply ell)

lemma sphereCotangentRepresentative_restriction (x : Base) (ell : SphereCotangent x) :
    sphereCovectorRestriction x (sphereCotangentRepresentative x ell) = ell := by
  ext v
  exact sphereCotangentRepresentative_pair x ell v

lemma sphereCotangentRepresentative_orthogonal (x : Base) (ell : SphereCotangent x) :
    ⟪(x:AmbientBase),sphereCotangentRepresentative x ell⟫ = 0 := by
  have h := sphere_derivative_radial_orthogonal x ((sphereRoundMusical x).symm ell)
  simpa [sphereCotangentRepresentative,PiLp.inner_apply,dotProduct,mul_comm] using h

lemma sphereCotangentRepresentative_unique (x : Base) (ell : SphereCotangent x)
    (v : AmbientBase) (hr : sphereCovectorRestriction x v = ell)
    (ho : ⟪(x:AmbientBase),v⟫ = 0) : sphereCotangentRepresentative x ell = v := by
  apply sub_eq_zero.mp
  apply sphereCovectorRestriction_separates x
  · rw [map_sub,sphereCotangentRepresentative_restriction,hr,sub_self]
  · rw [inner_sub_right,sphereCotangentRepresentative_orthogonal,ho,sub_self]

lemma sphereCotangentRepresentative_project (x : Base) (v : AmbientBase) :
    sphereCotangentRepresentative x (sphereCovectorRestriction x v) = sphereTangentProjection x v :=
  sphereCotangentRepresentative_unique x _ _ (sphereTangentProjection_restriction x v)
    (sphereTangentProjection_orthogonal x v)

def roundCotangentTensor : IntrinsicTensor := fun x ↦
  bilinearPullback (innerSL ℝ) (sphereCotangentRepresentative x)

lemma roundCotangentTensor_apply (x : Base) (v w : SphereCotangent x) :
    roundCotangentTensor x v w =
      ⟪sphereCotangentRepresentative x v,sphereCotangentRepresentative x w⟫ := rfl

lemma roundCotangentTensor_symm (x : Base) (v w : SphereCotangent x) :
    roundCotangentTensor x v w = roundCotangentTensor x w v := by
  simp only [roundCotangentTensor_apply]
  exact real_inner_comm _ _

lemma roundCotangentTensor_pos (x : Base) (v : SphereCotangent x) (hv : v ≠ 0) :
    0 < roundCotangentTensor x v v := by
  rw [roundCotangentTensor_apply]
  apply real_inner_self_pos.mpr
  intro h
  have hh := sphereCotangentRepresentative_restriction x v
  rw [h,map_zero] at hh
  exact hv hh.symm

lemma roundCotangentTensor_restriction (x : Base) (v w : AmbientBase) :
    roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) =
      ⟪sphereTangentProjection x v,sphereTangentProjection x w⟫ := by
  rw [roundCotangentTensor_apply,sphereCotangentRepresentative_project,sphereCotangentRepresentative_project]

lemma roundCotangentTensor_tangent (x : Base) (v w : AmbientBase)
    (hv : ⟪(x:AmbientBase),v⟫ = 0) (hw : ⟪(x:AmbientBase),w⟫ = 0) :
    roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫ := by
  simp [roundCotangentTensor_restriction,sphereTangentProjection,hv,hw]

lemma roundCotangentTensor_ambient (x : Base) : intrinsicAmbientMatrix roundCotangentTensor x = 1 :=
  intrinsicAmbientMatrix_reference _ x (roundCotangentTensor_tangent x)

end
end Yau.Target

end OAI
