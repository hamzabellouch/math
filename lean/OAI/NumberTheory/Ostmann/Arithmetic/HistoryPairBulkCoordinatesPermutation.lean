import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesMatching
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesOrder
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionPermutation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairGiantCoordinates HistoryActiveCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def matching_of_assignments (sources : SourceFamily) (T : List SourceSlot)
    (h k : History l) (hh : Template.Matches T h.root.small) (hk : Template.Matches T k.root.small)
    (x y : SourceAssignment sources T)
    (hx : h.root.small = assignedSlots sources T x) (hy : k.root.small = assignedSlots sources T y)
    (π : Equiv.Perm (Fin T.length))
    (hv : ∀ i, (y i : ℕ) = (x (π i) : ℕ))
    (hb : ∀ i, T[i].role = .bulk ↔ T[π i].role = .bulk) : RootMatching h k where
  positions := ((matchedRootPosition hk).symm.trans π).trans (matchedRootPosition hh)
  value := by
    intro i
    obtain ⟨j,rfl⟩ := (matchedRootPosition hk).surjective i
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [matchedRootPosition_value hk y hy, matchedRootPosition_value hh x hx, hv]
  bulk := by
    intro i
    obtain ⟨j,rfl⟩ := (matchedRootPosition hk).surjective i
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, matchedRootPosition_role]
    exact hb j

theorem leafBulkPermutation_bulk_iff (m k₀ l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin m))
    (i : Fin (Template.current (Template.initial m k₀) l).length) :
    (Template.current (Template.initial m k₀) l)[i].role = .bulk ↔
      (Template.current (Template.initial m k₀) l)[leafBulkPermutation m k₀ l σ i].role = .bulk := by
  change ((Template.current (Template.initial m k₀) l).get i).role = .bulk ↔
    ((Template.current (Template.initial m k₀) l).get (leafBulkPermutation m k₀ l σ i)).role = .bulk
  by_cases hi : (Template.current (Template.initial m k₀) l)[i].role = .bulk
  · have he := leafBulkPermutation_apply_bulk m k₀ l σ ⟨i,hi⟩
    rw [he]
    exact iff_of_true hi ((currentBulkPositionEquiv m k₀ l).symm
      (σ (currentBulkPositionEquiv m k₀ l ⟨i,hi⟩))).property
  · rw [leafBulkPermutation_apply_nonbulk m k₀ l σ i hi]

def permutationMatching (b k₀ : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k₀ → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l))
    (h k : History l)
    (hh : Template.Matches (Template.current (Template.initial (2*b) k₀) l) h.root.small)
    (hk : Template.Matches (Template.current (Template.initial (2*b) k₀) l) k.root.small)
    (hx : h.root.small = assignedSlots (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l) x)
    (hy : k.root.small = assignedSlots (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l)
      (leafBulkAssignmentPermutation b k₀ l bulk top comp σ x)) : RootMatching h k :=
  matching_of_assignments _ _ h k hh hk x _ hx hy (leafBulkPermutation (2*b) k₀ l σ)
    (leafBulkAssignmentPermutation_val b k₀ l bulk top comp σ x)
    (leafBulkPermutation_bulk_iff (2*b) k₀ l σ)

theorem ordered_right_key (b k₀ : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k₀ → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l))
    (h k : History l)
    (hh : Template.Matches (Template.current (Template.initial (2*b) k₀) l) h.root.small)
    (hk : Template.Matches (Template.current (Template.initial (2*b) k₀) l) k.root.small)
    (hx : h.root.small = assignedSlots (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l) x)
    (hy : k.root.small = assignedSlots (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l)
      (leafBulkAssignmentPermutation b k₀ l bulk top comp σ x))
    (u : Fin (2^l) × Fin (2*b)) :
    rightMap h k (.inr (.inl (matchedRootPosition hk
      ((currentBulkPositionEquiv (2*b) k₀ l).symm u).val))) =
      orderedKey (2*b) k₀ h k hh (σ u) := by
  have he := (permutationMatching b k₀ bulk top comp σ x h k hh hk hx hy).key_eq
    (matchedRootPosition hk ((currentBulkPositionEquiv (2*b) k₀ l).symm u).val)
  simpa only [permutationMatching, matching_of_assignments, Equiv.trans_apply,
    Equiv.symm_apply_apply, leafBulkPermutation_apply_leaf, orderedKey] using he

theorem insertOrdered_right (b k₀ : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k₀ → Fin 2 → PrimeSource)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l))
    (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial (2*b) k₀) l) h.root.small)
    (hk : Template.Matches (Template.current (Template.initial (2*b) k₀) l) k.root.small)
    (hx : h.root.small = assignedSlots (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l) x)
    (hy : k.root.small = assignedSlots (initialSourceFamily b k₀ bulk top comp)
      (Template.current (Template.initial (2*b) k₀) l)
      (leafBulkAssignmentPermutation b k₀ l bulk top comp σ x))
    (z : Fin (2^l) × Fin (2*b) → ℝ) (u : Fin (2^l) × Fin (2*b)) :
    insertOrdered (2*b) k₀ h k hs hh z
      (rightMap h k (.inr (.inl (matchedRootPosition hk
        ((currentBulkPositionEquiv (2*b) k₀ l).symm u).val)))) = z (σ u) := by
  rw [ordered_right_key b k₀ bulk top comp σ x h k hh hk hx hy]
  exact insertOrdered_left (2*b) k₀ h k hs hh z (σ u)

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI
