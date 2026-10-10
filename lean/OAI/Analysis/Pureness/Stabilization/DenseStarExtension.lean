import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI
noncomputable section
open scoped Topology
namespace CuntzTrace
variable {D B : Type*} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra B]

def extendDenseStarHom (S : NonUnitalStarSubalgebra ℂ D) (f : S →⋆ₙₐ[ℂ] B)
    (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (hd : DenseRange (fun x : S => (x : D))) : D →⋆ₙₐ[ℂ] B := by
  let l : S →ₗ[ℂ] B := { toFun := f, map_add' := f.map_add, map_smul' := f.map_smul }
  let L : S →L[ℂ] B := l.mkContinuous 1 (fun x => by simpa [l] using hf x)
  let E : D →L[ℂ] B := L.extend S.toSubmodule.subtypeL
  have heq (x : S) : E (x : D) = f x :=
    ContinuousLinearMap.extend_eq L (e := S.toSubmodule.subtypeL) hd isometry_subtype_coe.isUniformInducing x
  exact {
    toFun := E
    map_zero' := E.map_zero
    map_add' := E.map_add
    map_smul' := E.map_smul
    map_mul' := by
      refine hd.induction_on₂ ?_ ?_
      · exact isClosed_eq (E.continuous.comp continuous_mul)
          ((E.continuous.comp continuous_fst).mul (E.continuous.comp continuous_snd))
      · intro x y
        change E ((x*y : S) : D) = E (x : D)*E (y : D)
        rw [heq,heq,heq,map_mul]
    map_star' := by
      intro a
      refine hd.induction_on a ?_ ?_
      · exact isClosed_eq (E.continuous.comp continuous_star) E.continuous.star
      · intro x
        change E ((star x : S) : D) = star (E (x : D))
        rw [heq,heq,map_star] }

theorem extendDenseStarHom_eq (S : NonUnitalStarSubalgebra ℂ D) (f : S →⋆ₙₐ[ℂ] B)
    (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (hd : DenseRange (fun x : S => (x : D))) (x : S) :
    extendDenseStarHom S f hf hd (x : D) = f x :=
  ContinuousLinearMap.extend_eq _ hd isometry_subtype_coe.isUniformInducing x
end CuntzTrace

end

end OAI
