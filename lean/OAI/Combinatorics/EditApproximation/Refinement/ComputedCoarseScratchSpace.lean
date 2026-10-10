import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialAllocation
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseHistorySpace
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseBitWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

def physicalCoarseAllocationEntry {M J B : ℕ} [NeZero B] (source target : List ℕ) (N : ℕ)
    (depth : PhysicalEntry M J target.length → ℕ) (draw : PhysicalCoarseDraw source target B depth)
    (entry : PhysicalEntry M J target.length) : ℕ :=
  BinaryFraction.coarseIndexedInitialAllocation (inputHeight N ^ 4) (64 * inputHeight N) N
    (Nat.pos_of_neZero B) (pow_pos (Nat.two_pow_pos _) _)
    (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
    (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (draw entry)

theorem physicalCoarseAllocationEntry_fits {M J : ℕ} :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, ∀ (_hB : NeZero B),
      ∀ (source target : List ℕ) (depth : PhysicalEntry M J target.length → ℕ),
      B = (integerParameters N).B →
      (∀ entry, depth entry = computedCoarseDepth N
        (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi))) →
      source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (draw : PhysicalCoarseDraw source target B depth) (entry : PhysicalEntry M J target.length),
        physicalCoarseAllocationEntry source target N depth draw entry ≤ (N + 2) ^ 181 := by
  filter_upwards [BinaryFraction.computedCoarseIndexedInitialAllocation_polynomial] with N hN
  intro B inst source target depth hB hd hsize hsymbols draw entry
  have hx := physicalSource_length_le source entry.1
  have hy : (substring target entry.2.lo entry.2.hi).length ≤ target.length := by
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  have hs : ∀ a ∈ physicalSource source entry.1 ++ substring target entry.2.lo entry.2.hi,
      Nat.size a ≤ inputHeight N ^ 3 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hsymbols a (List.mem_append_left _ (physicalSource_mem source entry.1 a ha))
    · exact hsymbols a (List.mem_append_right _ (List.mem_of_mem_take (List.mem_of_mem_drop ha)))
  exact hN B (depth entry) (physicalSource source entry.1)
    (substring target entry.2.lo entry.2.hi) hB (hd entry)
    (max_le (by omega) (by omega)) hs (Nat.pos_of_neZero B)
    (pow_pos (Nat.two_pow_pos _) _) (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (draw entry)

/-- Reserve every fresh cell allocated by every coarse cache miss until
termination. This deliberately bounds more than simultaneously live scratch. -/


theorem computedFamilyCoarseScratchCapacity_eq (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseScratchCapacity source target N input =
      ((computedFamilyResult source target N input).freshKeys.map
        (coarseHistoryKeyCost (fun _ => (N + 2) ^ 181))).sum :=
  computedFamilyKernelWork_eq_fresh_sum source target N input _

theorem computedFamilyCoarseScratchCapacity_bound (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseScratchCapacity source target N input ≤
      (N + 2) ^ 181 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  exact coarseHistoryKeyCost_le _ _ (fun _ => le_rfl)

theorem computedFamilyCoarseScratchCapacity_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseScratchCapacity source target N input ≤ (N + 2) ^ 183 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 181 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseScratchCapacity_bound source target N input
    _ ≤ (N + 2) ^ 181 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
