import OAI.Algebra.AuslanderReiten.Stable.SourceStableShift
import OAI.Algebra.AuslanderReiten.Duality.ProjectiveStablePairing

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))

open CompleteComparison

noncomputable def fullHomSymmetricDuality
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K)) (a : ℤ) :
    Module.Dual k (CohomologyClass K K a) ≃ₗ[k] CohomologyClass K K (-a - 1) := by
  let E := fullHomStableLinearEquiv (k := k) K K a hK
    (hK.toExactProjectiveComplex.cochainShift a)
  let D := τ.completeStableDuality hs (chainOfCochain K) hK.toExactProjectiveComplex
    (N := Cokernel (chainOfCochain (K⟦a⟧)) 0)
  let B := StableHom.targetEquiv (k := k)
    (M := Cokernel (chainOfCochain (K⟦a⟧)) 0)
    (shiftedCokernelEquiv K (-1) 1 rfl).symm
  let C := fullHomStableZeroLinearEquiv (k := k) (K⟦a⟧) (K⟦(-1 : ℤ)⟧)
    (hK.cochainShift a) (hK.toExactProjectiveComplex.cochainShift (-1))
  let L := leftShiftCohomologyEquiv k K (K⟦(-1 : ℤ)⟧) (-a) a 0 (by omega)
  let T := rightShiftCohomologyEquiv k K K (-a - 1) (-1) (-a) (by omega)
  exact E.symm.dualMap.trans (D.trans (B.trans (C.symm.trans (L.symm.trans T.symm))))

end ArExplicit.FrobeniusTrace

end OAI
