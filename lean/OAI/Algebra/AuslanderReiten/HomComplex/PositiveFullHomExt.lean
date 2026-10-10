import OAI.Algebra.AuslanderReiten.Stable.SourceStableShift
import OAI.Algebra.AuslanderReiten.Stable.StableExtEquiv

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

def fullPositiveExtEquiv (n : ℕ) :
    CohomologyClass K L ((n+1 : ℕ) : ℤ) ≃ₗ[k]
      Abelian.Ext (ModuleCat.of R (Cokernel (chainOfCochain K) 0))
        (ModuleCat.of R (Cokernel (chainOfCochain L) 0)) (n+1) :=
  (fullHomSourceStableLinearEquiv (k := k) K L ((n+1 : ℕ) : ℤ) hK hL).trans
    (positiveExtStableEquiv (k := k) hK
      (ModuleCat.of R (Cokernel (chainOfCochain L) 0)) n).symm

theorem fullPositiveExtEquiv_stable (n : ℕ)
    (x : CohomologyClass K L ((n+1 : ℕ) : ℤ)) :
    positiveExtStableEquiv (k := k) hK
      (ModuleCat.of R (Cokernel (chainOfCochain L) 0)) n
      (fullPositiveExtEquiv (k := k) K L hK hL n x) =
    fullHomSourceStableLinearEquiv (k := k) K L ((n+1 : ℕ) : ℤ) hK hL x :=
  LinearEquiv.apply_symm_apply _ _

end ArExplicit.CompleteComparison

end

end OAI
