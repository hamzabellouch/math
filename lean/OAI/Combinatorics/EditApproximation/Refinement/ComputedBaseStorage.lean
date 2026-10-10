import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseCopySpace
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseHistorySpace

namespace OAI

namespace EditApproximation
open Filter

/-- Retained dictionary, all copied coarse inputs, all coarse-array
capacities, and all local workspace allocations. Summing all allocations
is a conservative bound on simultaneous storage. -/
noncomputable def computedFamilyStorageCapacity (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N)
    (localSpace : ComputedFamilyMemoKey source target N → ℕ) : ℕ :=
  (computedFamilyResult source target N input).memory.rationalStorage +
    computedFamilyCoarseCopyStorage source target N input +
    computedFamilyCoarseArrayCapacity source target N input +
    computedFamilyKernelWork source target N input localSpace

theorem computedFamilyKernelWork_polynomial (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
        (cost : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, cost key ≤ computedLocalKernelBudget D N) →
      computedFamilyKernelWork source target N input cost ≤ (N + 2) ^ 2 := by
  filter_upwards [computedFamilyKernelWork_near_linear D 1 (by norm_num)] with N hN
  intro source target hsize input cost hcost
  have h := hN source target hsize input cost hcost
  norm_num at h
  exact_mod_cast h

private theorem storage_sum_bound (X K cache copied arrays localWork : ℕ)
    (hX : 2 ≤ X) (hK : 39 ≤ K)
    (hcache : cache ≤ X ^ K) (hcopy : copied ≤ X ^ 18)
    (harray : arrays ≤ X ^ 39) (hlocal : localWork ≤ X ^ 2) :
    cache + copied + arrays + localWork ≤ X ^ (K + 2) := by
  have hbase : 0 < X := by omega
  have hc := hcopy.trans (Nat.pow_le_pow_right hbase (show 18 ≤ K by omega))
  have ha := harray.trans (Nat.pow_le_pow_right hbase hK)
  have hl := hlocal.trans (Nat.pow_le_pow_right hbase (show 2 ≤ K by omega))
  calc
    _ ≤ 4 * X ^ K := by omega
    _ ≤ X ^ 2 * X ^ K := Nat.mul_le_mul_right _ (by nlinarith only [hX])
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem computedFamilyStorageCapacity_polynomial (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (input : ComputedFamilyInput source target N)
        (localSpace : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, localSpace key ≤ computedLocalKernelBudget D N) →
      computedFamilyStorageCapacity source target N input localSpace ≤ (N + 2) ^ (65556 + 2) := by
  filter_upwards [computedFamilyCoarseCopyStorage_polynomial,
    computedFamilyCoarseArrayCapacity_polynomial, computedFamilyKernelWork_polynomial D,
    computed_localOnlineMassBound_word, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))]
    with N hcopy harray hlocal hmass hN hell
  intro source target hsize hsymbols input localSpace hcost
  have hcache := computedFamilyResult_retained_storage source target N (by omega) hell hsize hmass input
  have hc := hcopy source target hsize hsymbols input
  have ha := harray source target hsize input
  have hl := hlocal source target hsize input localSpace hcost
  exact storage_sum_bound (N + 2) 65556 _ _ _ _ (by omega) (by decide)
    hcache hc ha hl

end EditApproximation

end OAI
