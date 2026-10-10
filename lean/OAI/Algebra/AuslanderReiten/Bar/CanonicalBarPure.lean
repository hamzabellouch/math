import OAI.Algebra.AuslanderReiten.Bar.CanonicalBarTermValues

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

def canonicalPure (a b : R) (x : X) :
    (ExternalBalanced.factorEvaluation k X (AbsoluteBar.complex k R)).X 0 :=
  BalancedTensor.tmul (⟨a ⊗ₜ[k] b⟩ :
    EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 1)) x

def coefficientPure (a : R) (x : X) : (ModuleBar.complex k R X).X 0 :=
  a ⊗ₜ[k] x

omit [CharP k 2] in
theorem rawEval_pure (a b : R) (x : X) :
    rawEval k R X 1 ((a ⊗ₜ[k] b) ⊗ₜ[k] x) = a ⊗ₜ[k] (b • x) := by
  rw [rawEval_succ, rawEval_zero]

theorem canonicalComplexIso_pure (a b : R) (x : X) :
    type_of% ((canonicalComplexIso_tmul k R X 0
      (⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 1)) x).trans
        (rawEval_pure k R X a b x)) :=
  (canonicalComplexIso_tmul k R X 0
    (⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 1)) x).trans
      (rawEval_pure k R X a b x)

end ArExplicit.BarBalanced

end

end OAI
