import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TorusCoefficientFinite
import OAI.GroupTheory.SimpleAmenable.Homology.TranslationCoefficients

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a : ℕ} {K : Type} [AddCommGroup K]
lemma tensorEquiv_translation (u : CutRing × CutRing) (v : SquareStep a ⊗[ℤ] K) :
    (BooleanStep.tensorEquiv (a:=a) (K:=K))
      ((SquareStep.coefficientRep a K).ρ (SquareStep.orbitProjection (Multiplicative.ofAdd u)) v) =
      stepTranslate (K:=K) u ((BooleanStep.tensorEquiv (a:=a) (K:=K)) v) := by
  induction v using TensorProduct.inductionOn with
  | add left right left_eq right_eq =>
    let action : (SquareStep a ⊗[ℤ] K) →ₗ[ℤ] (SquareStep a ⊗[ℤ] K) :=
      (SquareStep.coefficientRep a K).ρ (SquareStep.orbitProjection (Multiplicative.ofAdd u))
    change BooleanStep.tensorEquiv (a:=a) (K:=K) (action (left + right)) = _
    change BooleanStep.tensorEquiv (a:=a) (K:=K) (action left) = _ at left_eq
    change BooleanStep.tensorEquiv (a:=a) (K:=K) (action right) = _ at right_eq
    simp only [map_add,left_eq,right_eq]
  | tmul f k =>
    change (BooleanStep.tensorMap (a:=a) (K:=K))
      (SquareStep.orbitRepresentation a (SquareStep.orbitProjection (Multiplicative.ofAdd u)) f ⊗ₜ[ℤ] k) = _
    rw [←SquareStep.representation_reduce]
    apply Subtype.ext
    funext p
    rfl
lemma tensorEquiv_symm_translation (u : CutRing × CutRing) (v : BooleanStep a K) :
    (BooleanStep.tensorEquiv (a:=a) (K:=K)).symm (stepTranslate (K:=K) u v) =
    (SquareStep.coefficientRep a K).ρ (SquareStep.orbitProjection (Multiplicative.ofAdd u))
      ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v) := by
  apply (BooleanStep.tensorEquiv (a:=a) (K:=K)).injective
  rw [LinearEquiv.apply_symm_apply,tensorEquiv_translation,LinearEquiv.apply_symm_apply]
@[simp] lemma stepTranslate_zero (v : BooleanStep a K) : stepTranslate (K:=K) 0 v=v := by
  apply Subtype.ext
  funext p
  change v.val (SimpleAmenable.translate a (-0) p)=v.val p
  simp
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
