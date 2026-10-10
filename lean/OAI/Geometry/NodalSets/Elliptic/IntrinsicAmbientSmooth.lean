import OAI.Geometry.NodalSets.Elliptic.IntrinsicAmbientExtension

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

local instance : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance : TopologicalSpace (TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

abbrev IntrinsicTensorSmooth (A : IntrinsicTensor) : Prop :=
  ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
      (E := fun x ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) x (A x))

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)

include hA in
lemma intrinsic_restriction_pairing_smooth (v w : AmbientBase) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞
      (fun x ↦ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)) := by
  have h := hA.clm_bundle_apply₂ (sphereCovectorRestriction_smooth v)
    (sphereCovectorRestriction_smooth w)
  intro x
  have hh := (contMDiffAt_totalSpace.mp (h x)).2
  simpa using hh

include hA in
lemma intrinsicAmbientMatrix_smooth (i j : Fin 5) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ intrinsicAmbientMatrix A x i j) := by
  let v := EuclideanSpace.basisFun (Fin 5) ℝ i
  let w := EuclideanSpace.basisFun (Fin 5) ℝ j
  have hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ ⟪(x : AmbientBase),v⟫) := by
    have h := (innerSL ℝ v).contMDiff.comp (contMDiff_coe_sphere (n := 4) (m := ∞))
    convert h using 1
    first | rfl | (funext x; exact real_inner_comm _ _)
  have hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ ⟪(x : AmbientBase),w⟫) := by
    have h := (innerSL ℝ w).contMDiff.comp (contMDiff_coe_sphere (n := 4) (m := ∞))
    convert h using 1
    first | rfl | (funext x; exact real_inner_comm _ _)
  exact (intrinsic_restriction_pairing_smooth A hA v w).add (hv.smul hw)

end
end Yau.Target

end OAI
