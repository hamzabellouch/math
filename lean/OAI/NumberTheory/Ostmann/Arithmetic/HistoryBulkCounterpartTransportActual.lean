import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCounterpartTransportIndependent
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorizationDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkCounterpartTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryPairBulkTransport
open HistoryBulkReferenceScalarCoordinates HistoryBulkGiantCorrectedBounds
open HistoryGiantOriginalMeanFactorization
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (s t : ℤ) (gp gm : ℕ)
  (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
  (hold : ∀ i, (y₀ i).val = (x₀ (π i)).val)
  (hnew : ∀ i, (y i).val = (x (π i)).val)
  (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l) {outside : List ℕ}
  (hs : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c).Supported (frequencyBound Bs BD Bz k L) outside)
  (ks : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e).Supported (frequencyBound Bs BD Bz k L) outside)
  (hfixed : ∀ i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,
    ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role ≠ .bulk → (x i).val = (x₀ i).val)
  (Xp Xm : ℤ)
include hold hnew hfixed

theorem independent_counterpart_mul_jointScalar (sc : ℕ) :
    counterpart C y Xm *
      jointScalar C sc (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e) hs ks (boolEquiv (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e)) (orderedEquiv (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e) hs (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c))) (fun u : Bool => if u then (Xm : ℝ) else (Xp : ℝ)) (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x) =
    jointCorrectedScalar C sc (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e) hs ks (boolEquiv (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e)) (orderedEquiv (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e) hs (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c))) (fun u : Bool => if u then (Xm : ℝ) else (Xp : ℝ)) (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x) := by
  have ht := independent_new_counterpart_mul_pairedRealXi C.sources (2*(bulkSize k L/2)) k (frequencyBound Bs BD Bz k L) l
    s t gp gm x₀ y₀ x y π hold hnew c e hs ks hfixed Xp Xm
    (l+1) (bulkSize k L/2) sc
    ((C.giantCenter : ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
    (C.compensationLogScale l) C.scale C.bulkBin C.spectatorBin C.giantCenter
    (C.cells.center (bulkSize k L/2))
  simp only [insertOrderedGiants_eq_bulk_over_giants] at ht
  exact ht

end Ostmann.Arithmetic.HistoryBulkCounterpartTransport

end

end OAI
