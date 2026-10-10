import Mathlib
import OAI.Analysis.WeakInfiniteness.ApproximateCut
import OAI.Analysis.WeakInfiniteness.TensorFunctoriality

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

namespace WeakPureInfiniteness

universe u v

section TensorCut

variable {A : Type u} {C : Type v} [CStarAlgebra A] [NonUnitalCStarAlgebra C]

def rightElementaryHom : C →⋆ₙₐ[ℂ] MinimalTensor A C where
  toFun c := minimalElementary 1 c
  map_zero' := Subtype.ext (spatialElementary_zero_right 1)
  map_add' _ _ := Subtype.ext (spatialElementary_add_right _ _ _)
  map_smul' _ _ := Subtype.ext (spatialElementary_smul_right _ _ _)
  map_mul' x y := by
    apply Subtype.ext
    change spatialElementary 1 (x*y) = spatialElementary (1 : A) x * spatialElementary 1 y
    simpa only [one_mul] using spatialElementary_mul (1 : A) 1 x y
  map_star' x := by
    apply Subtype.ext
    change spatialElementary 1 (star x) = star (spatialElementary (1 : A) x)
    simpa only [star_one] using spatialElementary_star (1 : A) x

@[simp] lemma rightElementaryHom_apply (c : C) :
    rightElementaryHom (A := A) c = minimalElementary 1 c := rfl

def tensorCut (c : C) (x : MinimalTensor A C) : MinimalTensor A C :=
  x - x * rightElementaryHom c

lemma norm_tensorCut_le [PartialOrder C] [StarOrderedRing C]
    (e : C) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (x : MinimalTensor A C) :
    ‖tensorCut e x‖ ≤ ‖x‖ := by
  let := CStarAlgebra.spectralOrder (MinimalTensor A C)
  let := CStarAlgebra.spectralOrderedRing (MinimalTensor A C)
  exact norm_sub_mul_of_pos_contraction x (rightElementaryHom e)
    (map_nonneg (rightElementaryHom (A := A)) he)
    ((NonUnitalStarAlgHom.norm_apply_le (rightElementaryHom (A := A)) e).trans hen)

lemma tensorCut_elementary (e c : C) (a : A) :
    tensorCut e (minimalElementary a c) = minimalElementary a (c - c * e) := by
  apply Subtype.ext
  change spatialElementary a c - spatialElementary a c * spatialElementary 1 e = _
  rw [← spatialElementary_mul, mul_one]
  have h := spatialElementary_add_right a (c-c*e) (c*e)
  rw [sub_add_cancel] at h
  exact sub_eq_iff_eq_add.mpr h

end TensorCut

end WeakPureInfiniteness
end

end OAI
