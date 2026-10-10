import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShift
import OAI.Algebra.AuslanderReiten.Cones.CokernelShift
import OAI.Algebra.AuslanderReiten.Complete.CompleteShiftDual
import OAI.Algebra.AuslanderReiten.Stable.StableHomEquiv

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace ArExplicit.CompleteComparison

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]

noncomputable def fullHomStableZeroLinearEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L 0 ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0) :=
  (fullHomStableLinearEquiv K L 0 hK (hL.cochainShift 0)).trans
    (StableHom.targetEquiv (k := k) (shiftedCokernelEquiv L 0 0 rfl))

noncomputable def fullHomSourceStableLinearEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L n ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) n) (Cokernel (chainOfCochain L) 0) :=
  (leftShiftCohomologyEquiv k K L n (-n) 0 (by omega)).trans
    ((fullHomStableZeroLinearEquiv (K⟦-n⟧) L (hK.cochainShift (-n)) hL).trans
      (StableHom.sourceEquiv (k := k) (shiftedCokernelEquiv K (-n) n rfl).symm))

end ArExplicit.CompleteComparison

end OAI
