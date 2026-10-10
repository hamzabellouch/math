import OAI.Algebra.AuslanderReiten.Stable.RawSourceCoordinates
import OAI.Algebra.AuslanderReiten.Stable.StableIsomorphism

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

def rawSourceStableEquiv : CohomologyClass K L 1 ≃+ StableHom R (RawSyzygy K) (CochainCokernel L) :=
  (fullHomSourceStableLinearEquiv (k := k) K L 1 hK hL).toAddEquiv.trans
    (((StableIsomorphism.ofLinearEquiv (rawSyzygyEquiv K).symm).sourceAddEquiv).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv L)).targetAddEquiv)

@[simp]
theorem rawSourceStableEquiv_mk (x : Cocycle K L 1) :
    rawSourceStableEquiv (k := k) K L hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (rawSourceCocycleMap x) := by
  simp only [rawSourceStableEquiv, AddEquiv.trans_apply,
    LinearEquiv.coe_toAddEquiv,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  erw [fullHomSourceStableLinearEquiv_mk hK hL x]
  rw [StableHom.comp_classOf, StableHom.comp_classOf]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
