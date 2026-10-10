import Mathlib
import OAI.Analysis.WeakInfiniteness.ApproximateCut
import OAI.Analysis.WeakInfiniteness.TensorInjectivity

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u v

noncomputable section

open scoped TensorProduct ENNReal ComplexOrder

open UniformSpace Filter Topology

variable {A B : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def spatialRightMultiplier (c : C) : SpatialAmbient A C :=
  ⟨fun π => (TensorProduct.mapL (1 : π.left →L[ℂ] π.left) (π.rightRep c)).completion,
    memℓp_infty ⟨‖c‖, by
      rintro _ ⟨π,rfl⟩
      dsimp only
      rw [norm_completion]
      exact (TensorProduct.norm_mapL_le _ _).trans
        ((mul_le_mul ContinuousLinearMap.norm_id_le (NonUnitalStarAlgHom.norm_apply_le π.rightRep c)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _))⟩⟩

def spatialRightMultiplierHom : C →⋆ₙₐ[ℂ] SpatialAmbient A C where
  toFun := spatialRightMultiplier
  map_zero' := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL _ (π.rightRep 0)).completion=0
    simp [completion_zero]
  map_add' c d := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL _ (π.rightRep (c+d))).completion=_+_
    rw [map_add, TensorProduct.mapL_add_right, completion_add]
    rfl
  map_smul' r c := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL _ (π.rightRep (r • c))).completion=r • _
    rw [map_smul, TensorProduct.mapL_smul_right, completion_smul]
    rfl
  map_mul' c d := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL (1 : π.left →L[ℂ] π.left) (π.rightRep (c*d))).completion=_*_
    rw [map_mul, ← one_mul (1 : π.left →L[ℂ] π.left), TensorProduct.mapL_mul]
    exact completion_comp _ _
  map_star' c := by
    apply Subtype.ext; funext π
    change (TensorProduct.mapL (1 : π.left →L[ℂ] π.left) (π.rightRep (star c))).completion=star _
    rw [map_star, ← star_one (π.left →L[ℂ] π.left)]
    exact (completion_mapL_star _ _).symm

lemma spatialElementary_mul_rightMultiplier (a : A) (c e : C) :
    spatialElementary a c * spatialRightMultiplier e=spatialElementary a (c*e) := by
  apply Subtype.ext; funext π
  change (TensorProduct.mapL (π.leftRep a) (π.rightRep c)).completion *
    (TensorProduct.mapL 1 (π.rightRep e)).completion =
      (TensorProduct.mapL (π.leftRep a) (π.rightRep (c*e))).completion
  rw [map_mul, ← mul_one (π.leftRep a), TensorProduct.mapL_mul]
  exact (completion_comp _ _).symm

lemma spatial_mul_rightMultiplier_mem (e : C) (x : MinimalTensor A C) :
    x.val * spatialRightMultiplier e ∈ minimalTensorSubalgebra A C := by
  have hs : ∀ z ∈ Submodule.span ℂ (Set.range fun p : A × C => spatialElementary p.1 p.2),
      z * spatialRightMultiplier e ∈ minimalTensorSubalgebra A C := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a,c⟩,rfl⟩ := hz
      rw [spatialElementary_mul_rightMultiplier]
      exact spatialElementary_mem a (c*e)
    | zero => simp only [zero_mul]; exact (minimalTensorSubalgebra A C).zero_mem
    | add z w _ _ hz hw => rw [add_mul]; exact (minimalTensorSubalgebra A C).add_mem hz hw
    | smul c z _ hz => rw [smul_mul_assoc]; exact (minimalTensorSubalgebra A C).smul_mem c hz
  have hc : IsClosed {z : SpatialAmbient A C | z*spatialRightMultiplier e ∈ minimalTensorSubalgebra A C} :=
    isClosed_closure.preimage (continuous_id.mul continuous_const)
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  exact (closure_minimal hs hc) hx

def tensorRightMultiply (e : C) (x : MinimalTensor A C) : MinimalTensor A C :=
  ⟨x.val * spatialRightMultiplier e, spatial_mul_rightMultiplier_mem e x⟩

def tensorCutNonunital (e : C) (x : MinimalTensor A C) : MinimalTensor A C :=
  x-tensorRightMultiply e x

lemma norm_tensorCutNonunital_le [PartialOrder C] [StarOrderedRing C]
    (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (x : MinimalTensor A C) :
    ‖tensorCutNonunital e x‖ ≤ ‖x‖ := by
  let := CStarAlgebra.spectralOrder (SpatialAmbient A C)
  let := CStarAlgebra.spectralOrderedRing (SpatialAmbient A C)
  exact norm_sub_mul_of_pos_contraction x.val (spatialRightMultiplierHom e)
    (map_nonneg (spatialRightMultiplierHom (A := A)) he)
    ((NonUnitalStarAlgHom.norm_apply_le (spatialRightMultiplierHom (A := A)) e).trans hen)

lemma tensorCutNonunital_elementary (e c : C) (a : A) :
    tensorCutNonunital e (minimalElementary a c)=minimalElementary a (c-c*e) := by
  apply Subtype.ext
  change spatialElementary a c-spatialElementary a c*spatialRightMultiplier e=_
  rw [spatialElementary_mul_rightMultiplier]
  have h := spatialElementary_add_right a (c-c*e) (c*e)
  rw [sub_add_cancel] at h
  exact sub_eq_iff_eq_add.mpr h

lemma spatialMapLeft_rightMultiplier (φ : A →⋆ₙₐ[ℂ] B) (e : C) :
    spatialMapLeft φ (spatialRightMultiplier e)=spatialRightMultiplier e := rfl

lemma minimalMapLeft_tensorCutNonunital (φ : A →⋆ₙₐ[ℂ] B) (e : C) (x : MinimalTensor A C) :
    minimalMapLeft φ (tensorCutNonunital e x)=tensorCutNonunital e (minimalMapLeft φ x) := by
  apply Subtype.ext
  change spatialMapLeft φ (x.val-x.val*spatialRightMultiplier e)=_
  rw [map_sub, map_mul, spatialMapLeft_rightMultiplier]
  rfl

end

end WeakPureInfiniteness
end

end OAI
