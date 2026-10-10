import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesRight
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalar

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding
open HistoryPairBulkTransport HistoryBulkSupportConversePlan HistoryBulkReferenceScalarCoordinates

theorem newSourceSample_assigned_actual (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s : ℤ) (gp gm : ℕ)
    (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) (i : Coordinate seed l) :
    (newSourceSample sources seed V l (assignedRoot sources _ s gp gm x) c
      (assignedRoot_matches sources _ s gp gm x) gp gm i : ℝ) =
    (coordinateSample seed (assignedHistory sources seed V l s gp gm x c)
      (assignedLabels sources seed V l s gp gm x c) i : ℝ) := by
  rcases i with t | i | i
  · cases t <;> simp only [newSourceSample_plus,newSourceSample_minus,
      coordinateSample_giant,assignedHistory,decodeHistory_root,assignedRoot,
      Bool.false_eq_true,↓reduceIte,Rat.cast_natCast,Int.cast_natCast]
  · rw [newSourceSample_assigned_root,assigned_root_sample]
    simp only [Rat.cast_natCast,Int.cast_natCast]
  · rw [newSourceSample_internal]
    change ((historyDraws sources seed V l c i).val:ℝ) =
      (coordinateSample seed (decodeHistory sources seed V l
        (assignedRoot sources _ s gp gm x) c)
        (decoded_tree_source_labels sources seed V l
          (assignedRoot sources _ s gp gm x) c
          (assignedRoot_matches sources _ s gp gm x)) (.inr (.inr i)) : ℝ)
    rw [decoded_coordinateSample_internal sources seed V l
      (assignedRoot sources _ s gp gm x) c
      (assignedRoot_matches sources _ s gp gm x) i,Int.cast_natCast]

theorem assigned_scalar_transport (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (s : ℤ) (gp gm gp' gm' : ℕ)
    (x₀ x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l)
    (hs : (assignedHistory sources seed V l s gp gm x₀ c).Supported V outside)
    (hs' : (assignedHistory sources seed V l s gp' gm' x c).Supported V outside)
    (bc sc : ℕ) (X tb td G : ℝ)
    (y : Key (assignedHistory sources seed V l s gp gm x₀ c) → ℝ)
    (hy : ∀i, y (decodedCoordinateEquiv sources seed V l
      (assignedRoot sources _ s gp gm x₀) c (assignedRoot_matches sources _ s gp gm x₀) i) =
      (newSourceSample sources seed V l (assignedRoot sources _ s gp' gm' x) c
        (assignedRoot_matches sources _ s gp' gm' x) gp' gm' i:ℝ)) :
    actualRealHistoryScalar bc sc X tb td G outside
      (assignedHistory sources seed V l s gp gm x₀ c) hs y =
    actualRealHistoryScalar bc sc X tb td G outside
      (assignedHistory sources seed V l s gp' gm' x c) hs'
      (fun i => (integerSample (assignedHistory sources seed V l s gp' gm' x c) i:ℝ)) := by
  apply actualRealHistoryScalar_eq_of_coordinates seed _ _ hs hs'
    (assignedLabels sources seed V l s gp gm x₀ c)
    (assignedLabels sources seed V l s gp' gm' x c)
    (decoded_plan_eq sources seed V outside l _ _ c c
      (assignedRoot_matches sources _ s gp gm x₀)
      (assignedRoot_matches sources _ s gp' gm' x) rfl rfl hs hs')
  intro i
  exact (hy i).trans (newSourceSample_assigned_actual sources seed V l s gp' gm' x c i)

end Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport

end

end OAI
