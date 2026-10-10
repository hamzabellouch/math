import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedHistory
import OAI.Combinatorics.EditApproximation.Refinement.ComputedFreshWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseExecution
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

def physicalCoarseHistoryEntry {M J B : ℕ} [NeZero B] (source target : List ℕ) (N : ℕ)
    (depth : PhysicalEntry M J target.length → ℕ) (draw : PhysicalCoarseDraw source target B depth)
    (entry : PhysicalEntry M J target.length) : ℕ :=
  BinaryFraction.coarseIndexedInitialArrayHistory N B (depth entry) (physicalSource source entry.1)
    (substring target entry.2.lo entry.2.hi) (draw entry)

/-- The complete indexed history of each call fits the reserved capacity. -/
theorem physicalCoarseHistoryEntry_fits {M J : ℕ} :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, ∀ (_hB : NeZero B),
      ∀ (source target : List ℕ) (depth : PhysicalEntry M J target.length → ℕ),
      B = (integerParameters N).B →
      (∀ entry, depth entry = computedCoarseDepth N
        (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi))) →
      source.length + target.length ≤ N →
      ∀ (draw : PhysicalCoarseDraw source target B depth) (entry : PhysicalEntry M J target.length),
        physicalCoarseHistoryEntry source target N depth draw entry ≤ (N + 2) ^ 37 := by
  filter_upwards [BinaryFraction.coarseIndexedInitialArrayHistory_polynomial] with N hN
  intro B inst source target depth hB hd hsize draw entry
  have hx := physicalSource_length_le source entry.1
  have hy : (substring target entry.2.lo entry.2.hi).length ≤ target.length := by
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  exact hN B (depth entry) (physicalSource source entry.1)
    (substring target entry.2.lo entry.2.hi) hB (hd entry)
    (max_le (by omega) (by omega)) inst (draw entry)

/-- Reserve a complete-history buffer at each actual coarse cache miss.
This conservatively retains those buffers until the memo run finishes. -/


theorem computedFamilyCoarseArrayCapacity_eq (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseArrayCapacity source target N input =
      ((computedFamilyResult source target N input).freshKeys.map
        (coarseHistoryKeyCost (fun _ => (N + 2) ^ 37))).sum :=
  computedFamilyKernelWork_eq_fresh_sum source target N input _

theorem computedFamilyCoarseArrayCapacity_bound (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseArrayCapacity source target N input ≤
      (N + 2) ^ 37 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  exact coarseHistoryKeyCost_le _ _ (fun _ => le_rfl)

theorem computedFamilyCoarseArrayCapacity_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseArrayCapacity source target N input ≤ (N + 2) ^ 39 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 37 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseArrayCapacity_bound source target N input
    _ ≤ (N + 2) ^ 37 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
