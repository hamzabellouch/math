import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupProgramCost
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmupCost

namespace OAI

namespace EditApproximation
open BinaryFraction

theorem queryWarmupProgram_width {ι : Type*} {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F B : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (q : TargetInterval ny) (oracle : ι → BinaryFraction)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, ((initialRead r).value oracle).width ≤ B)
    (hc : ∀ r, ((childRead r).value oracle).width ≤ B) :
    ((queryWarmupProgram parent N P F a initialRead childRead q).value oracle).width ≤
      localWarmupWordBudget M B := by
  let value := (initialRead q).value oracle
  let centers := queryRawCentersWithWork N P F a value q
  let words := centers.1.map fun r => (initialRead r).value oracle
  let initial := queryOverrideParentReadWithWork value q centers.1 words
  let inputs := queryWarmupInputsWithWork M parent N P F a initial q
  let childWords := inputs.1.map fun input => (childRead input).value oracle
  let child := fun input : Fin M × TargetInterval ny => queryChildReadWithWork inputs.1 childWords input.1 input.2
  have hiW : ∀ r, (initial r).1.width ≤ B := by
    intro r
    unfold initial queryOverrideParentReadWithWork
    dsimp only
    split_ifs
    · exact hi q
    · exact gatheredWordLookupWithWork_width _ centers.1 words r B (by omega) (by
        intro w hw
        obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
        exact hi key)
  have hcW : ∀ input, (child input).1.width ≤ B := by
    intro input
    exact gatheredWordLookupWithWork_width _ inputs.1 childWords input B (by omega) (by
      intro w hw
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
      exact hc key)
  have hw := (localWarmupKernelWithWork_bounds parent N P F B hP hFpos a
    (fun r => (initial r).1) (fun input => (child input).1) q hB hN hnx hny hM hPb hF ha hiW hcW).1
  rw [← localWarmupReadKernelWithWork_eq parent N P F a initial child q
    (16 * Nat.size ny + 7 + centers.1.length * (16 * Nat.size ny + 6))
    (queryOverrideParentReadWithWork_cost value q centers.1 words)] at hw
  simpa only [queryWarmupProgram, BitQuery.value_bind, BitQuery.value_collect,
    BitQuery.compute, BitQuery.value] using hw

theorem queryChargedWarmup_width (source target : List ℕ) {M J passes copies T S : ℕ}
    (N P F B : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (oracle : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
    (hB : 10 ≤ B) (hP : 0 < P) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hs : Nat.size source.length + 2 ≤ B) (ht : Nat.size target.length + 2 ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) :
    ((queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits).value
      oracle).width ≤ localWarmupWordBudget M B := by
  have hi (q : TargetInterval target.length) := queryPhysicalInitial_width source target N P F B A a
    multiplier parent occurrence symbolBits positionBits oracle q hP ht' hinit
  have hsmall : B ≤ localWarmupWordBudget M B := by
    unfold localWarmupWordBudget physicalContinuationInputBudget
    dsimp only
    omega
  unfold queryChargedWarmup
  simp only [BitQuery.value]
  split
  · exact (hi _).trans hsmall
  · split
    · split
      · exact (hi _).trans hsmall
      · exact queryWarmupProgram_width _ N P F B hP a _ _ _ oracle hB hN hF hFpos hPb hs ht hM ha hi
          (fun _ => hv _)
    · exact (hi _).trans hsmall

end EditApproximation

end OAI
