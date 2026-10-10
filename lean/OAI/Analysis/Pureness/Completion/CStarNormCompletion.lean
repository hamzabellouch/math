import OAI.Analysis.Pureness.Completion.CStarAlgebraNorm
import OAI.Analysis.Pureness.Completion.NonUnitalCStarCompletion

namespace OAI
noncomputable section
namespace CuntzPureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

abbrev Completion (p : CStarAlgebraNorm R) :=
  letI := p.normedRing
  UniformSpace.Completion R

instance completionCStarAlgebra (p : CStarAlgebraNorm R) : NonUnitalCStarAlgebra p.Completion := by
  letI := p.normedRing
  letI := p.normedAlgebra
  letI := p.cstarRing
  exact CuntzPureness.nonUnitalCompletionCStarAlgebra R

def completionMap (p : CStarAlgebraNorm R) : R →⋆ₙₐ[ℂ] p.Completion := by
  letI := p.normedRing
  letI := p.normedAlgebra
  letI := p.cstarRing
  exact
    { toFun := fun x => (x : UniformSpace.Completion R)
      map_zero' := UniformSpace.Completion.coe_zero
      map_add' := UniformSpace.Completion.coe_add
      map_smul' := UniformSpace.Completion.coe_smul
      map_mul' := CuntzPureness.completion_coe_mul R
      map_star' := CuntzPureness.completion_coe_star R }

lemma completionMap_norm (p : CStarAlgebraNorm R) (x : R) :
    ‖p.completionMap x‖ = p.toAlgebraNorm x := by
  let := p.normedRing
  let := p.normedAlgebra
  let := p.cstarRing
  exact UniformSpace.Completion.norm_coe x

lemma completionMap_injective (p : CStarAlgebraNorm R) : Function.Injective p.completionMap := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply p.toAlgebraNorm.eq_zero_of_map_eq_zero'
  change p.toAlgebraNorm x = 0
  rw [← completionMap_norm, hx, norm_zero]

theorem eq_original {A : Type*} [CStarAlgebra A] (p : CStarAlgebraNorm A) (a : A) :
    p.toAlgebraNorm a = ‖a‖ := by
  rw [← completionMap_norm]
  exact NonUnitalStarAlgHom.norm_map p.completionMap p.completionMap_injective a
end CuntzPureness.CStarAlgebraNorm

end

end OAI
