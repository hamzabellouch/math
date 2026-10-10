import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainMixedData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainPrimeData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualRootReferenceFamily HistoryBulkActualPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem plainPrimeCollisionPrincipal_eq_background (guarded : Bool) :
    plainCollisionPrincipal C spectator ds hactual hl σ false hV guarded =
    backgroundCollisionMean C (spectatorList spectator ds)
      (plainPrimeReferences C spectator ds hactual hl σ hV)
      (plainPrimeMask C spectator ds hactual hl σ) false false guarded := rfl

theorem plainMixedCollisionPrincipal_eq_background (guarded : Bool) :
    plainCollisionPrincipal C spectator ds hactual hl σ true hV guarded =
    backgroundCollisionMean C (spectatorList spectator ds)
      (plainMixedReferences C spectator ds hactual hl σ hV)
      (plainMixedMask C spectator ds hactual hl σ) false true guarded := rfl
theorem plainPrimeCollisionPrincipal_error_le {ε θ : ℝ}
    (h : ‖backgroundCollisionMean C (spectatorList spectator ds)
      (plainPrimeReferences C spectator ds hactual hl σ hV)
      (plainPrimeMask C spectator ds hactual hl σ) false false true-backgroundCollisionMean C (spectatorList spectator ds)
      (plainPrimeReferences C spectator ds hactual hl σ hV)
      (plainPrimeMask C spectator ds hactual hl σ) false false false‖≤ε ∧
      ‖backgroundCollisionMean C (spectatorList spectator ds)
      (plainPrimeReferences C spectator ds hactual hl σ hV)
      (plainPrimeMask C spectator ds hactual hl σ) false false true-backgroundCollisionMean C (spectatorList spectator ds)
      (plainPrimeReferences C spectator ds hactual hl σ hV)
      (plainPrimeMask C spectator ds hactual hl σ) false false false‖≤θ) :
    ‖plainCollisionPrincipal C spectator ds hactual hl σ false hV true-
      plainCollisionPrincipal C spectator ds hactual hl σ false hV false‖≤ε ∧
    ‖plainCollisionPrincipal C spectator ds hactual hl σ false hV true-
      plainCollisionPrincipal C spectator ds hactual hl σ false hV false‖≤θ :=
  error_bounds_of_eq
    (plainPrimeCollisionPrincipal_eq_background C spectator ds hactual hl σ hV true)
    (plainPrimeCollisionPrincipal_eq_background C spectator ds hactual hl σ hV false) h

theorem plainMixedCollisionPrincipal_error_le {ε θ : ℝ}
    (h : ‖backgroundCollisionMean C (spectatorList spectator ds)
      (plainMixedReferences C spectator ds hactual hl σ hV)
      (plainMixedMask C spectator ds hactual hl σ) false true true-backgroundCollisionMean C (spectatorList spectator ds)
      (plainMixedReferences C spectator ds hactual hl σ hV)
      (plainMixedMask C spectator ds hactual hl σ) false true false‖≤ε ∧
      ‖backgroundCollisionMean C (spectatorList spectator ds)
      (plainMixedReferences C spectator ds hactual hl σ hV)
      (plainMixedMask C spectator ds hactual hl σ) false true true-backgroundCollisionMean C (spectatorList spectator ds)
      (plainMixedReferences C spectator ds hactual hl σ hV)
      (plainMixedMask C spectator ds hactual hl σ) false true false‖≤θ) :
    ‖plainCollisionPrincipal C spectator ds hactual hl σ true hV true-
      plainCollisionPrincipal C spectator ds hactual hl σ true hV false‖≤ε ∧
    ‖plainCollisionPrincipal C spectator ds hactual hl σ true hV true-
      plainCollisionPrincipal C spectator ds hactual hl σ true hV false‖≤θ :=
  error_bounds_of_eq
    (plainMixedCollisionPrincipal_eq_background C spectator ds hactual hl σ hV true)
    (plainMixedCollisionPrincipal_eq_background C spectator ds hactual hl σ hV false) h

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
