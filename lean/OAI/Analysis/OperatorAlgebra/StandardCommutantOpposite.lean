import OAI.Analysis.OperatorAlgebra.AntiunitaryOperatorIdentities
import OAI.Analysis.ModularRecovery.ModularCovariance
import OAI.Analysis.WeakInfiniteness.TensorSubalgebras

namespace OAI

/-! The actual opposite-algebra identification of a standard commutant. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma antiunitaryConjugate_one (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    antiunitaryConjugate J 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact hJ x

def antiunitaryOppositeHom (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    (H →L[ℂ] H)ᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun a := antiunitaryConjugate J (star a.unop)
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [MulOpposite.unop_zero, star_zero, antiunitaryConjugate_apply,
      zero_apply, map_zero]
  map_one' := by
    simpa only [MulOpposite.unop_one, star_one] using antiunitaryConjugate_one J hJ
  map_add' a b := by
    simp only [MulOpposite.unop_add, star_add, antiunitaryConjugate_add]
  map_mul' a b := by
    simp only [MulOpposite.unop_mul, star_mul, antiunitaryConjugate_mul J hJ]
  commutes' c := by
    change antiunitaryConjugate J (star (c • (1 : H →L[ℂ] H))) = c • 1
    rw [star_smul, star_one, antiunitaryConjugate_smul, star_star,
      antiunitaryConjugate_one J hJ]
  map_star' a := by
    change antiunitaryConjugate J (star (star a.unop)) =
      star (antiunitaryConjugate J (star a.unop))
    exact antiunitaryConjugate_star J hJ (star a.unop)

lemma antiunitaryOppositeHom_involutive (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (a : H →L[ℂ] H) :
    antiunitaryOppositeHom J hJ
      (MulOpposite.op (antiunitaryOppositeHom J hJ (MulOpposite.op a))) = a := by
  change antiunitaryConjugate J (star (antiunitaryConjugate J (star a))) = a
  rw [← antiunitaryConjugate_star J hJ, star_star,
    antiunitaryConjugate_involutive J hJ]

def standardOppositeInclusion (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Sᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H)ᵐᵒᵖ where
  __ := S.subtype.toAlgHom.op
  map_star' a := congrArg MulOpposite.op (map_star S.subtype a.unop)

lemma standardConjugate_mem (S : StandardModularData H)
    (a : S.M.toStarSubalgebraᵐᵒᵖ) :
    antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op a.unop.val) ∈ S.M.commutant := by
  change S.jConjugate (star a.unop.val) ∈ S.M.commutant
  exact S.jConjugate_mem_commutant (star a.unop.val)
    (show star a.unop.val ∈ S.M from star_mem a.unop.property)

def standardCommutantHom (S : StandardModularData H) :
    S.M.toStarSubalgebraᵐᵒᵖ →⋆ₐ[ℂ] S.M.commutant.toStarSubalgebra :=
  ((antiunitaryOppositeHom S.J S.conjugation).comp
    (standardOppositeInclusion S.M.toStarSubalgebra)).codRestrict
      S.M.commutant.toStarSubalgebra (standardConjugate_mem S)

lemma standardCommutantHom_apply (S : StandardModularData H)
    (a : S.M.toStarSubalgebraᵐᵒᵖ) :
    (standardCommutantHom S a).val =
      antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op a.unop.val) := rfl

lemma standardCommutantHom_bijective (S : StandardModularData H) :
    Function.Bijective (standardCommutantHom S) := by
  constructor
  · intro a b h
    apply MulOpposite.unop_injective
    apply Subtype.ext
    have he := congrArg
      (fun c : S.M.commutant.toStarSubalgebra =>
        antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op c.val)) h
    change antiunitaryOppositeHom S.J S.conjugation
      (MulOpposite.op (antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op a.unop.val))) =
      antiunitaryOppositeHom S.J S.conjugation
      (MulOpposite.op (antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op b.unop.val))) at he
    simpa only [antiunitaryOppositeHom_involutive] using he
  · intro b
    have hb : antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op b.val) ∈ S.M := by
      change S.jConjugate (star b.val) ∈ S.M
      exact S.jConjugate_mem (star b.val)
        (show star b.val ∈ S.M.commutant from star_mem b.property)
    let a : S.M.toStarSubalgebra :=
      ⟨antiunitaryOppositeHom S.J S.conjugation (MulOpposite.op b.val), hb⟩
    refine ⟨MulOpposite.op a, ?_⟩
    apply Subtype.ext
    exact antiunitaryOppositeHom_involutive S.J S.conjugation b.val

def standardCommutantEquiv (S : StandardModularData H) :
    S.M.toStarSubalgebraᵐᵒᵖ ≃⋆ₐ[ℂ] S.M.commutant.toStarSubalgebra :=
  StarAlgEquiv.ofBijective (standardCommutantHom S) (standardCommutantHom_bijective S)

end WeakPureInfiniteness

end

end OAI
