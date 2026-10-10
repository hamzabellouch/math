import OAI.Algebra.AuslanderReiten.Ext.ATwistedTensorExt
import OAI.Algebra.AuslanderReiten.Tensor.TwistedEnvelopingProjective
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorPositiveAction
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCompleteInverse
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomZero

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]

abbrev completeTwistIn := BalancedTensor.completeActionIn (AFrobeniusTrace k q)
  (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

abbrev completeTwistOut := BalancedTensor.completeActionOut (AFrobeniusTrace k q)
  (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem nativeEvaluationIso_eq :
    BalancedTensor.nativeEvaluationIso (A.simpleFiniteModule q) (evaluatedTwistEquiv q H) =
      evaluatedTwistIso q H := rfl

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem completeTwist_inverse :
    (HomotopyCategory.quotient _ _).map (completeTwistIn q H ≫ completeTwistOut q H) = 𝟙 _ :=
  BalancedTensor.completeAction_inverse (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem completeTwistIn_quotient :
    (HomotopyCategory.quotient _ _).map (completeTwistIn q H) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)).inv :=
  BalancedTensor.completeActionIn_quotient (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem completeTwistOut_quotient :
    (HomotopyCategory.quotient _ _).map (completeTwistOut q H) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)).hom :=
  BalancedTensor.completeActionOut_quotient (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

theorem completeTwist_scalar (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (hp : Resolution.NoPositivePowerOne q) (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    fullHomPostcomp (completeTwistOut q H) _
      (fullHomPrecomp (completeTwistIn q H) _
        (mapFullHom (evaluatedTwistFunctor q H) _ _ _ x)) = (((H⁻¹ : kˣ) : k)^m) • x := by
  apply BalancedTensor.completeAction_scalar_positive (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H) (3*m) (by omega)
  intro z
  rw [nativeEvaluationIso_eq]
  exact evaluatedTwistExt_scalar q H hq hq1 hp m z

end ArExplicit.T

end

end OAI
