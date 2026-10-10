import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesLeft
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsInsertion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion
open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairBulkTransport
open HistoryBulkFibreGiantApproximation HistoryPairReferenceSourceTransport
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

theorem fixedB_root (f : Frame (l:=l) C outside) (x : Frame.Source (C:=C) (l:=l))
    (hfixed : ∀j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,
      ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get j).role ≠ .bulk →
        (x j).val = (f.leftSource j).val)
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    f.fixedB x (rootKey f.left f.right (rootPosition (leftDraw f) j)) = ((x j).val : ℤ) := by
  have he := insertOrderedGiants_left_coordinate C.sources (2*(bulkSize k L/2)) k
    (frequencyBound Bs BD Bz k L) l f.s f.P.toNat f.Q.toNat 1 1
    f.leftSource x f.leftChoices f.right f.left_supported hfixed 0 0 (.inr (.inl j))
  have hc := congrFun (integerInsertOrderedGiants_cast (2*(bulkSize k L/2)) k
    f.left f.right f.left_supported
    (root_matches (assignedLabels C.sources _ _ l f.s f.P.toNat f.Q.toNat f.leftSource f.leftChoices))
    (orderedIntegerSourceValues C.sources (2*(bulkSize k L/2)) k l x) (fun _ => 0))
    (rootKey f.left f.right (rootPosition (leftDraw f) j))
  simp only [orderedIntegerSourceValues_cast,Int.cast_zero] at hc
  simp only [newSourceSample_assigned_root,Rat.cast_natCast,ite_self,Int.cast_zero] at he
  have hh : (f.fixedB x (rootKey f.left f.right (rootPosition (leftDraw f) j)) : ℝ) =
      ((x j).val : ℝ) := hc.trans he
  exact_mod_cast hh

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
