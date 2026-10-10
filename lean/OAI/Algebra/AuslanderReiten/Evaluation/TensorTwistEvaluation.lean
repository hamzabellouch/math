import OAI.Algebra.AuslanderReiten.Modules.TwistedModuleEvaluation
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeEvaluation
import OAI.Algebra.AuslanderReiten.Fibers.ExplicitBimoduleFiber
import OAI.Algebra.AuslanderReiten.Algebras.TSimpleTwist

namespace OAI

noncomputable section
namespace ArExplicit.T
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "X" => A.simpleFiniteModule q

theorem sourceTwist_smul_simple (a : A k q) (x : A.Simple q) :
    sourceTwist q H a • x = a • x := by
  change ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
      (sourceTwist q H a) x =
    ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) a x
  induction a using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add]
    change (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
      (sourceTwist q H a)) x +
      (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
      (sourceTwist q H b)) x =
      (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) a) x +
      (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) b) x
    rw [ha, hb]
  | tmul a b =>
    let y : Resolution.Simple q ⊗[k] Resolution.Simple q := x
    change ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
        (sourceTwist q H (a ⊗ₜ[k] b)) y =
      ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) (a ⊗ₜ[k] b) y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul s t => rfl

theorem sourceInverseTwist_smul_simple (a : A k q) (x : A.Simple q) :
    (sourceTwist q H).symm a • x = a • x := by
  have h := sourceTwist_smul_simple q H ((sourceTwist q H).symm a) x
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

def twistedSimpleEquiv : TwistedLeftModule k (A k q) (sourceTwist q H) (X).carrier ≃ₗ[A k q]
    (X).carrier where
  toFun := TwistedLeftModule.value
  invFun := TwistedLeftModule.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := sourceInverseTwist_smul_simple q H a x.value

def evaluatedTwistEquiv : (FiniteLeftModule.evaluated X (twistedFiniteModule (sourceTwist q H))).carrier ≃ₗ[A k q]
    (X).carrier :=
  (FiniteLeftModule.twistedEvaluationEquiv (sourceTwist q H) X).trans (twistedSimpleEquiv q H)

@[simp] theorem evaluatedTwistEquiv_tmul
    (r : EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier)
    (x : (X).carrier) :
    evaluatedTwistEquiv q H (BalancedTensor.tmul r x) = (sourceTwist q H).symm r.value.value • x := rfl

theorem evaluatedTwistEquiv_unit (x : (X).carrier) :
    evaluatedTwistEquiv q H (BalancedTensor.tmul
      (⟨⟨1⟩⟩ : EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier) x) = x := by
  rw [evaluatedTwistEquiv_tmul, map_one, one_smul]

end ArExplicit.T

end

end OAI
