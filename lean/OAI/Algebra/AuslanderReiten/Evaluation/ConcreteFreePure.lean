import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteFreeInput
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluatedFreeValues
import OAI.Algebra.AuslanderReiten.Evaluation.TensorFreeEvaluationCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "X" => ModuleCat.of A M
local notation "Y" => ModuleCat.of B N
local notation "P" => AbsoluteBar.complex k A
local notation "Q" => AbsoluteBar.complex k B

-- State the generic value in the canonical-input presentation used by endpoint insertion.
private theorem totalFreeEvaluation_canonical_pure (a b : A) (c d : B) (m : M) (n : N) :
    totalFreeEvaluation k A B M N e f
      ((productEvaluation k A B X Y).map
        (ExternalTensor.inclusion k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B) P Q 0 0 0 rfl)
        (BalancedTensor.tmul
          ((bimoduleCoordinates k A B ((P).X 0) ((Q).X 0)).symm
            ((⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k A ((P).X 0)) ⊗ₜ[k]
             (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k B ((Q).X 0))))
          (ExternalTensor.canonicalTmul k A B M N m n))) =
      (e (b • m) • a) ⊗ₜ[k] (f (d • n) • c) :=
  totalFreeEvaluation_pure k A B M N e f a b c d m n

end ArExplicit.ExternalBalanced

namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {k : Type u} [fieldK : Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)
local notation "R" => T k q
local notation "S" => Resolution.Simple q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local instance (priority := 3000) pureNativeScalar : Module k (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).scalar
local instance (priority := 3000) pureNativeTower : IsScalarTower k (A k q) (A.simpleFiniteModule q).carrier :=
  (A.simpleFiniteModule q).tower

private theorem endpointEvaluation_pure (a b c d : R) (s t : S) :
    endpointEvaluation q s t
      ((endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) =
    A.barZeroCoordinate q (squareEvaluation q s t ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) := by
  rw [endpointEvaluation_eq, LinearEquiv.apply_symm_apply]

-- Retain the additive structure and quotient relation of the concrete simple module.
-- Inferring the relation from its carrier avoids rebuilding it with another
-- presentation of the inherited additive monoid.
local notation "nativeSimpleAddCommGroup" =>
  (@Submodule.Quotient.addCommGroup (BaseAlgebra k q) (Resolution.F q) _
    (@Submodule.addCommGroup (BaseAlgebra k q) (BaseAlgebra k q) _
      (@BaseAlgebra.instAddCommGroup k q
        (@Ring.toAddCommGroup k (@DivisionRing.toRing k
          (@Field.toDivisionRing k fieldK)))) _ (Resolution.F q)) _ _)

private theorem evaluatedPairValue (a b c d : R) (s t : S) :
    type_of% ((@ExternalBalanced.totalFreeEvaluation_canonical_pure k R R S S
      _ _ _ _ _ _ nativeSimpleAddCommGroup nativeSimpleAddCommGroup _ _ _ _ _ _
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)
      a b c d s t).trans (freePair_evaluation q hq a b c d s t)) :=
  (@ExternalBalanced.totalFreeEvaluation_canonical_pure k R R S S
      _ _ _ _ _ _ nativeSimpleAddCommGroup nativeSimpleAddCommGroup _ _ _ _ _ _
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)
    a b c d s t).trans (freePair_evaluation q hq a b c d s t)

private theorem rawEndpointPairValue (a b c d : R) (s t : S) :
    type_of% ((freeCoordinateRaw_pure_inclusion q hq a b c d s t).trans
      (evaluatedPairValue q hq a b c d s t)) :=
  (freeCoordinateRaw_pure_inclusion q hq a b c d s t).trans
    (evaluatedPairValue q hq a b c d s t)

theorem freeCoordinateRaw_endpoint_pure (a b c d : R) (s t : S) :
    type_of% ((rawEndpointPairValue q hq a b c d s t).trans
      (endpointEvaluation_pure q a b c d s t).symm) :=
  (rawEndpointPairValue q hq a b c d s t).trans
    (endpointEvaluation_pure q a b c d s t).symm

end ArExplicit.T

end

end OAI
