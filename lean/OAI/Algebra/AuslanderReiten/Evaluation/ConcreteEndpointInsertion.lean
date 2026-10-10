import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEndpointCoordinates
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEvaluatedBase
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarPure

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "S" => Resolution.Simple q
local notation "X" => ModuleCat.of R S
local notation "P" => AbsoluteBar.complex k R

theorem endpointCoordinates_insert (a b c d : R) (s t : S) :
    BalancedTensor.tmul
      (⟨(endpointCoordinates q).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))⟩ :
        EnvelopingBimodule k (A k q) ((shuffledBarComplex q).X 0))
      (ExternalTensor.canonicalTmul k R R S S s t) =
    (ExternalBalanced.productEvaluation k R R X X).map
      (ExternalTensor.inclusion k Te Te P P 0 0 0 rfl)
      (BalancedTensor.tmul
        ((ExternalBalanced.bimoduleCoordinates k R R ((P).X 0) ((P).X 0)).symm
          ((⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k R ((P).X 0)) ⊗ₜ[k]
           (⟨c ⊗ₜ[k] d⟩ : EnvelopingBimodule k R ((P).X 0))))
        (ExternalTensor.canonicalTmul k R R S S s t)) := by
  rw [endpointCoordinates_symm]
  rfl

end ArExplicit.T

end

end OAI
