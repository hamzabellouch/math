import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanIntegerSample
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesFrozen
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryActiveCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def insertOrderedGiants (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℝ) (u : Bool → ℝ) : PairKey h k → ℝ :=
  HistoryActiveCoordinates.insert (giantCoordinates h k) (insertOrdered m k₀ h k hs hh z)
    (fun i => u ((boolEquiv h k).symm i))

theorem giant_bulk_disjoint (h k : History l) :
    Disjoint (giantCoordinates h k) (bulkCoordinates h k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hb
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
  exact left_giant_not_mem h k b hb

theorem insertOrderedGiants_eq_bulk_over_giants
    (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℝ) (u : Bool → ℝ) :
    insertOrderedGiants m k₀ h k hs hh z u =
      HistoryActiveCoordinates.insert (bulkCoordinates h k) (insertGiants h k u)
        (fun i => z ((orderedEquiv m k₀ h k hs hh).symm i)) := by
  funext i
  by_cases hg : i ∈ giantCoordinates h k
  · have hb : i ∉ bulkCoordinates h k :=
      fun hb => Finset.disjoint_left.mp (giant_bulk_disjoint h k) hg hb
    simp only [insertOrderedGiants,insertOrdered,insertGiants,HistoryActiveCoordinates.insert,dite_eq_left hg,dite_eq_right hb]
  · by_cases hb : i ∈ bulkCoordinates h k
    · simp only [insertOrderedGiants,insertOrdered,insertGiants,HistoryActiveCoordinates.insert,dite_eq_right hg,dite_eq_left hb]
    · simp only [insertOrderedGiants,insertOrdered,insertGiants,HistoryActiveCoordinates.insert,dite_eq_right hg,dite_eq_right hb]

@[simp] theorem insertOrderedGiants_left_giant
    (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℝ) (u : Bool → ℝ) (t : Bool) :
    insertOrderedGiants m k₀ h k hs hh z u (leftMap h k (.inl t)) = u t := by
  unfold insertOrderedGiants HistoryActiveCoordinates.insert
  rw [dite_eq_left (giant_mem h k t)]
  change u ((boolEquiv h k).symm (boolEquiv h k t)) = u t
  rw [Equiv.symm_apply_apply]

@[simp] theorem insertOrderedGiants_right_giant
    (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℝ) (u : Bool → ℝ) (t : Bool) :
    insertOrderedGiants m k₀ h k hs hh z u (rightMap h k (.inl t)) = u t := by
  rw [←shared_giant]
  exact insertOrderedGiants_left_giant m k₀ h k hs hh z u t

@[simp] theorem insertOrderedGiants_left_small
    (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℝ) (u : Bool → ℝ)
    (i : Fin h.root.small.length ⊕ InternalKey h) :
    insertOrderedGiants m k₀ h k hs hh z u (leftMap h k (.inr i)) =
      insertOrdered m k₀ h k hs hh z (leftMap h k (.inr i)) := by
  simp only [insertOrderedGiants,HistoryActiveCoordinates.insert,dite_eq_right (left_small_not_mem h k i)]

@[simp] theorem insertOrderedGiants_right_small
    (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
    (z : Fin (2^l) × Fin m → ℝ) (u : Bool → ℝ)
    (i : Fin k.root.small.length ⊕ InternalKey k) :
    insertOrderedGiants m k₀ h k hs hh z u (rightMap h k (.inr i)) =
      insertOrdered m k₀ h k hs hh z (rightMap h k (.inr i)) := by
  simp only [insertOrderedGiants,HistoryActiveCoordinates.insert,dite_eq_right (right_small_not_mem h k i)]

def orderedSourceValues (sources : SourceFamily) (m k₀ l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k₀) l)) :
    Fin (2^l) × Fin m → ℝ :=
  fun j => ((x ((Conclusion.currentBulkPositionEquiv m k₀ l).symm j).val).val : ℝ)

end Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinates

end

end OAI
