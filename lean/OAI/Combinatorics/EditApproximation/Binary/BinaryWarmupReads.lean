import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalWarmupKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The warmup continuation evaluates finite input-table lookups and
charges their scan costs at the point where each returned word is used. -/

namespace EditApproximation
namespace BinaryFraction



theorem localWarmupReadKernelWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (query : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) :
    (localWarmupReadKernelWithWork parent N P F a initial child query).1 =
      (localWarmupKernelWithWork parent N P F a (fun r => (initial r).1)
        (fun input => (child input).1) query).1 := by
  have hr := (localRepresentativeReadWithWork_eq_cost N P F a initial query R hR).1
  simp only [localWarmupReadKernelWithWork, localWarmupKernelWithWork, hr, bellmanReadWithWork_eq]

theorem localWarmupReadKernelWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (query : TargetInterval ny)
    (I C : ℕ) (hi : ∀ r, (initial r).2 ≤ I) (hc : ∀ input, (child input).2 ≤ C) :
    (localWarmupReadKernelWithWork parent N P F a initial child query).2 ≤
      (localWarmupKernelWithWork parent N P F a (fun r => (initial r).1)
        (fun input => (child input).1) query).2 * (I + M * (C + 3) + 4) := by
  let reps := localRepresentativesWithWork N P F a (fun r => (initial r).1) query
  let acts := wideActionsFromRepresentativesWithWork M parent reps.1 P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let result := bellmanWithWork endpointDistanceWithWork L.1 (initial query).1
    (fun input => (child input).1) query acts.1
  have hr := localRepresentativeReadWithWork_eq_cost N P F a initial query I hi
  have hb := bellmanReadWithWork_cost endpointDistanceWithWork L.1 (initial query).1
    child query acts.1 C (fun action _ i => hc (action.childState i))
  have hn := bellmanWithWork_action_count endpointDistanceWithWork L.1 (initial query).1
    (fun input => (child input).1) query acts.1
  have hquery := hi query
  have hr' : (localRepresentativeReadWithWork N P F a initial query).2 ≤ reps.2 * (I + 2) := hr.2
  have hb' : (bellmanReadWithWork endpointDistanceWithWork L.1 (initial query).1
      child query acts.1).2 ≤ result.2 + acts.1.length * (M * (C + 3)) := hb
  have hn' : acts.1.length ≤ result.2 := hn
  unfold localWarmupReadKernelWithWork
  dsimp only
  rw [hr.1]
  change (initial query).2 + (localRepresentativeReadWithWork N P F a initial query).2 +
    acts.2 + L.2 + (bellmanReadWithWork endpointDistanceWithWork L.1 (initial query).1
      child query acts.1).2 + 3 ≤
    (reps.2 + acts.2 + L.2 + result.2 + 3) * (I + M * (C + 3) + 4)
  have hh := Nat.mul_le_mul_right (M * (C + 3)) hn'
  have hrFactor := Nat.mul_le_mul_left reps.2
    (show I + 2 ≤ I + M * (C + 3) + 4 by omega)
  have haFactor : acts.2 ≤ acts.2 * (I + M * (C + 3) + 4) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left acts.2
      (show 1 ≤ I + M * (C + 3) + 4 by omega)
  have hLFactor : L.2 ≤ L.2 * (I + M * (C + 3) + 4) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left L.2
      (show 1 ≤ I + M * (C + 3) + 4 by omega)
  have hresultFactor : result.2 + result.2 * (M * (C + 3)) ≤
      result.2 * (I + M * (C + 3) + 4) := by
    calc
      _ = result.2 * (1 + M * (C + 3)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hconstant : I + 3 ≤ 3 * (I + M * (C + 3) + 4) := by omega
  nlinarith only [hr', hb', hquery, hh, hrFactor, haFactor, hLFactor, hresultFactor, hconstant]

def cachedLocalWarmupReadWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (query : TargetInterval ny) :
    BinaryFraction × ℕ :=
  finishCachedWithWork (localWarmupReadKernelWithWork parent N P F a initial child query)
    [true] (by decide) 0

theorem cachedLocalWarmupReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (query : TargetInterval ny)
    (I C : ℕ) (hi : ∀ r, (initial r).2 ≤ I) (hc : ∀ input, (child input).2 ≤ C) :
    (cachedLocalWarmupReadWithWork parent N P F a initial child query).1 =
      (cachedLocalWarmupKernelWithWork parent N P F a (fun r => (initial r).1)
        (fun input => (child input).1) query).1 ∧
    (cachedLocalWarmupReadWithWork parent N P F a initial child query).2 ≤
      (cachedLocalWarmupKernelWithWork parent N P F a (fun r => (initial r).1)
        (fun input => (child input).1) query).2 * (I + M * (C + 3) + 4) := by
  exact finishCachedWithWork_read_factor _ _ [true] (by decide) 0 _ (by omega)
    (localWarmupReadKernelWithWork_eq parent N P F a initial child query I hi)
    (localWarmupReadKernelWithWork_cost parent N P F a initial child query I C hi hc)

end BinaryFraction
end EditApproximation

end OAI
