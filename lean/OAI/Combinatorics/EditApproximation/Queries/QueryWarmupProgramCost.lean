import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryBandInputCost
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalWarmupWork

namespace OAI

namespace EditApproximation.BinaryFraction

def queryWarmupRepresentatives (P F B : ℕ) : ℕ := (B + 1) * (64 * F * P + 2) ^ 2

def queryWarmupInputsBitBudget (M P F B I : ℕ) : ℕ :=
  localRepresentativesBitBudget P F B * (I + 2) +
    queryWideInputsBitBudget M P (queryWarmupRepresentatives P F B) B + 1

theorem queryWarmupInputsWithWork_bounds {nx ny : ℕ} (M N P F B I : ℕ)
    (parent : TargetInterval nx) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hI : ∀ r, (initial r).2 ≤ I) :
    (queryWarmupInputsWithWork M parent N P F a initial q).1.length ≤
      queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2) ∧
    (queryWarmupInputsWithWork M parent N P F a initial q).2 ≤
      queryWarmupInputsBitBudget M P F B I := by
  let reps := localRepresentativeReadWithWork N P F a initial q
  have heq := (localRepresentativeReadWithWork_eq_cost N P F a initial q I hI).1
  have hlen : reps.1.length ≤ queryWarmupRepresentatives P F B := by
    rw [show reps.1 = _ from heq]
    exact localRepresentativesWithWork_length_le N P F B hP hFpos a _ q hN
  have hscale : ∀ br ∈ reps.1, br.1 ∈ dyadicScales N := by
    intro br hb
    rw [show reps.1 = _ from heq, localRepresentativesWithWork_value N P F hP] at hb
    exact (representativeList_conditions a.value (fun r => (initial r).1.value)
      (localRefinementRepresentatives_subset N P F a.value (fun r => (initial r).1.value) q br hb)).1
  have hw := queryWideInputsWithWork_dyadic_bounds M N P (queryWarmupRepresentatives P F B) B
    parent hP reps.1 hlen hscale hN hnx hny hM hPb
  have hr := localRepresentativeReadWithWork_cost N P F B I a initial q (by omega)
    hN hF hFpos hPb hP hny ha hi hI
  exact ⟨hw.1, Nat.add_le_add_right (Nat.add_le_add hr hw.2) 1⟩

def queryWarmupParentReadBudget (P F B : ℕ) : ℕ :=
  16 * B + 7 + queryWarmupRepresentatives P F B * (16 * B + 6)

def queryWarmupChildReadBudget (M P F B : ℕ) : ℕ :=
  1 + (queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (24 * B + 9)

def queryWarmupProgramBitBudget (M P F B C : ℕ) : ℕ :=
  C + queryRawCentersBitBudget P F B + queryWarmupRepresentatives P F B * (C + 3) +
    queryWarmupInputsBitBudget M P F B (queryWarmupParentReadBudget P F B) +
    (queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (C + 3) +
    localWarmupBitBudget M P F B *
      (queryWarmupParentReadBudget P F B + M * (queryWarmupChildReadBudget M P F B + 3) + 4)

end EditApproximation.BinaryFraction

namespace EditApproximation
open BinaryFraction

private theorem warmup_read_sum {κ : Type*} (keys : List κ) (cost : κ → ℕ) (C : ℕ)
    (hc : ∀ key, cost key ≤ C) : (keys.map cost).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have h := hc key
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryWarmupProgram_work_bound {ι : Type*} {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F B C : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (q : TargetInterval ny) (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, ((initialRead r).value oracle).width ≤ B)
    (hc : ∀ r, ((childRead r).value oracle).width ≤ B)
    (hiC : ∀ r, (initialRead r).work oracle readWork ≤ C)
    (hcC : ∀ r, (childRead r).work oracle readWork ≤ C) :
    (queryWarmupProgram parent N P F a initialRead childRead q).work oracle readWork ≤
      queryWarmupProgramBitBudget M P F B C := by
  let value := (initialRead q).value oracle
  let centers := queryRawCentersWithWork N P F a value q
  let words := centers.1.map fun r => (initialRead r).value oracle
  let initial := queryOverrideParentReadWithWork value q centers.1 words
  let inputs := queryWarmupInputsWithWork M parent N P F a initial q
  let childWords := inputs.1.map fun input => (childRead input).value oracle
  let child := fun input : Fin M × TargetInterval ny => queryChildReadWithWork inputs.1 childWords input.1 input.2
  have hcenters := queryRawCentersWithWork_bounds N P F B a value q (by omega) hN hF hFpos hP hPb
    (by omega) ha (hi q)
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
  have hiR : ∀ r, (initial r).2 ≤ queryWarmupParentReadBudget P F B := by
    intro r
    apply (queryOverrideParentReadWithWork_cost value q centers.1 words r).trans
    unfold queryWarmupParentReadBudget
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul hcenters.1 (by omega))
  have hinputs := queryWarmupInputsWithWork_bounds M N P F B _ parent hP a initial q (by omega)
    hN hF hFpos hPb (by omega) (by omega) hM ha hiW hiR
  have hcW : ∀ input, (child input).1.width ≤ B := by
    intro input
    exact gatheredWordLookupWithWork_width _ inputs.1 childWords input B (by omega) (by
      intro w hw
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
      exact hc key)
  have hcR : ∀ input, (child input).2 ≤ queryWarmupChildReadBudget M P F B := by
    intro input
    exact (queryChildReadWithWork_cost inputs.1 childWords input.1 input.2 B hM (by omega)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hinputs.1) 1)
  have hkernel := (localWarmupReadKernelWithWork_cost parent N P F a initial child q _ _ hiR hcR).trans
    (Nat.mul_le_mul_right _ (localWarmupKernelWithWork_bounds parent N P F B hP hFpos a
      (fun r => (initial r).1) (fun input => (child input).1) q hB hN hnx hny hM hPb hF ha hiW hcW).2)
  have hsumI := (warmup_read_sum centers.1 (fun r => (initialRead r).work oracle readWork + 3)
    (C + 3) (fun r => Nat.add_le_add_right (hiC r) 3)).trans (Nat.mul_le_mul_right _ hcenters.1)
  have hsumC := (warmup_read_sum inputs.1 (fun r => (childRead r).work oracle readWork + 3)
    (C + 3) (fun r => Nat.add_le_add_right (hcC r) 3)).trans (Nat.mul_le_mul_right _ hinputs.1)
  have hq := hiC q
  have hcentercost : centers.2 ≤ queryRawCentersBitBudget P F B := hcenters.2
  have hinputcost : inputs.2 ≤ queryWarmupInputsBitBudget M P F B (queryWarmupParentReadBudget P F B) := hinputs.2
  simp only [queryWarmupProgram, BitQuery.work_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero]
  change (initialRead q).work oracle readWork + (centers.2 +
    ((centers.1.map fun r => (initialRead r).work oracle readWork + 3).sum +
    (inputs.2 + ((inputs.1.map fun r => (childRead r).work oracle readWork + 3).sum +
    (localWarmupReadKernelWithWork parent N P F a initial child q).2)))) ≤ _
  calc
    _ ≤ C + (queryRawCentersBitBudget P F B +
        (queryWarmupRepresentatives P F B * (C + 3) +
        (queryWarmupInputsBitBudget M P F B (queryWarmupParentReadBudget P F B) +
        ((queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (C + 3) +
        localWarmupBitBudget M P F B *
          (queryWarmupParentReadBudget P F B + M * (queryWarmupChildReadBudget M P F B + 3) + 4))))) :=
      Nat.add_le_add hq (Nat.add_le_add hcentercost
        (Nat.add_le_add hsumI (Nat.add_le_add hinputcost (Nat.add_le_add hsumC hkernel))))
    _ = _ := by unfold queryWarmupProgramBitBudget; omega

end EditApproximation

end OAI
