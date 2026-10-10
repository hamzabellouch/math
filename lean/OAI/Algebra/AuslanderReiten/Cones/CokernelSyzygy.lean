import OAI.Algebra.AuslanderReiten.Complete.CompleteComparison
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ}

noncomputable def cokernelSyzygyEquiv (hP : ExactProjectiveComplex P) (n : ℤ) :
    Cokernel P (n + 1) ≃ₗ[R] LinearMap.ker (P.d n (n - 1)).hom := by
  have hex : LinearMap.range (P.d ((n + 1) + 1) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom :=
    hP.exactAt_of_indices rfl (by omega)
  exact (Submodule.quotEquivOfEq _ _ hex).trans
    ((P.d (n + 1) n).hom.quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (hP.exactAt n)))

end ArExplicit.CompleteComparison

end OAI
