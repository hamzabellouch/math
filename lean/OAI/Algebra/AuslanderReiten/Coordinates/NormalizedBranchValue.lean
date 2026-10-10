import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBranchTop

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)

omit [CharP k 2] in
theorem evaluatedTwistEquiv_symm (x : (A.simpleFiniteModule q).carrier) :
    (evaluatedTwistEquiv q H).symm x = BalancedTensor.tmul
      (⟨sourceUnit q H⟩ : EnvelopingBimodule k (A k q)
        (twistedFiniteModule (sourceTwist q H)).carrier) x := by
  apply (evaluatedTwistEquiv q H).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (evaluatedTwistEquiv_unit q H x).symm

theorem normalizedBranchTop_apply (x : (A.simpleFiniteModule q).carrier) :
    normalizedBranchTop q H x = BalancedTensor.tmul
      (⟨normalizedSourceTop q H (sourceUnit q H)⟩ : EnvelopingBimodule k (A k q)
        (TwoCone.baseCokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1).carrier) x := by
  unfold normalizedBranchTop
  erw [LinearMap.comp_apply, evaluatedTwistEquiv_symm]
  rfl

end ArExplicit.T

end

end OAI
