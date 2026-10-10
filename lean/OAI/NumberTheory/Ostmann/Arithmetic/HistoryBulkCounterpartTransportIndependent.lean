import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCounterpartTransportPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransportCoordinates

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkCounterpartTransport
open Construction Construction.CanonicalOccurrenceTransport
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryGiantReferenceCounterpart HistoryPairBulkTransport
open HistoryBulkReferenceScalarCoordinates HistoryBulkSupportConversePlan
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ → ℕ) (l : ℕ)
  (s t : ℤ) (gp gm : ℕ)
  (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hold : ∀ i, (y₀ i).val = (x₀ (π i)).val)
  (hnew : ∀ i, (y i).val = (x (π i)).val)
  (c e : HistoryChoices sources (Template.initial m k₀) V l) {outside : List ℕ}
  (hs : (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c).Supported V outside)
  (ks : (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e).Supported V outside)
  (hfixed : ∀ i : Fin (Template.current (Template.initial m k₀) l).length,
    ((Template.current (Template.initial m k₀) l).get i).role ≠ .bulk → (x i).val = (x₀ i).val)
  (Xp Xm : ℤ)
include hold hnew hfixed

theorem independent_new_counterpart_mul_pairedRealXi
    (j b sc : ℕ) (A B X tb td G : ℝ) (center : ℕ → ℝ) :
    (remainingCounterpartAt sources (Template.current (Template.initial m k₀) l) j A B G center
      (restoringAssignmentEquiv sources j _ y).1
      (restoringAssignmentEquiv sources j _ y).2 (Xm : ℝ) : ℂ) *
        pairedRealXi b sc X tb td G (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs ks (insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) (orderedSourceValues sources m k₀ l x) (fun u : Bool => if u then (Xm : ℝ) else (Xp : ℝ))) =
      correctedPairedRealXi b sc X tb td G (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs ks A B
        (pairedDiagonalHKeys (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) j) (pairedDiagonalUKeys (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) j)
        (Finset.univ : Finset (Fin (diagonalCellKeys (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) j).length))
        (pairedDiagonalCellCenter (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) j G center) (pairedDiagonalCellKey (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) j) (insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) (orderedSourceValues sources m k₀ l x) (fun u : Bool => if u then (Xm : ℝ) else (Xp : ℝ))) := by
  apply new_counterpart_mul_pairedRealXi sources (Template.initial m k₀) V l t gp gm
    y₀ y e (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) (orderedSourceValues sources m k₀ l x) (fun u : Bool => if u then (Xm : ℝ) else (Xp : ℝ))) (Xm : ℝ) ?_ ?_ hs ks j b sc A B X tb td G center
  · simpa only [↓reduceIte] using
      insertOrderedGiants_right_giant m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs
        (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
        (orderedSourceValues sources m k₀ l x)
        (fun u => if u then (Xm : ℝ) else (Xp : ℝ)) true
  · intro i
    simpa only [newSourceSample_assigned_root, Rat.cast_natCast] using
      HistoryBulkIndependentReferenceTransport.insertOrderedGiants_right_coordinate
        sources m k₀ V l s t gp gm gp gm x₀ y₀ x y π hold hnew c e hs hfixed
        Xp Xm (.inr (.inl i))

end Ostmann.Arithmetic.HistoryBulkCounterpartTransport

end

end OAI
