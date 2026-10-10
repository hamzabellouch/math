import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCheckRefinement
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorAllowance
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorWork

namespace OAI

/-! # A polynomial source-scan budget sufficient for the interrupted checker -/

namespace LowSpaceSubsetSum.BudgetedSeparatorCheck

open StoredSeparatorCheck

variable {n g : ℕ}

def factor (n : ℕ) : List (Block n g) → ℕ
  | [] => 64 * (n + 1) + 5
  | b :: rest => 4 * (b.queryBound + factor n rest + 40) + 4

private theorem factor_ge (blocks : List (Block n g)) : 4 ≤ factor n blocks := by
  cases blocks <;> simp only [factor] <;> omega

theorem reference_work (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (blocks : List (Block n g)) (xs ys : List (StoredEntry n)) :
    (reference capacity target blocks xs ys).2 ≤ factor n blocks *
      ((SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
        (blocks.map Block.source) xs ys).scans + xs.length + ys.length + 1) := by
  subst capacity
  induction blocks generalizing xs ys with
  | nil =>
    simp only [reference, List.map_nil, SeparatorBlocks.check, SeparatorTerminal.bounded, factor]
    split
    · simp only [BudgetedSeparatorTerminal.charge]
      nlinarith only [Nat.zero_le
        (SeparatorTerminal.run StoredEntry.value StoredEntry.value target xs ys).scans,
        Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length]
    · dsimp only
      nlinarith only [Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length]
  | cons b rest ih =>
    have hf := factor_ge rest
    simp only [reference, List.map_cons, SeparatorBlocks.check]
    split
    · have h := BudgetedSeparatorTraversal.reference_work b.queryBound (factor n rest)
        b.leftQuery b.rightQuery b.left b.right b.leftQuery_value b.rightQuery_value
        (fun _ as bs => reference (2 ^ n) target rest as bs)
        (fun _ as bs => SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
          (rest.map Block.source) as bs)
        (fun _ as bs => ih as bs) b.depth 0 b.familySize xs ys
      rw [b.depth_eq] at h
      change 4 + _ ≤ _
      simp only [factor, Block.source, SeparatorBlocks.depth] at h ⊢
      rw [b.depth_eq]
      nlinarith only [h, hf, Nat.zero_le xs.length, Nat.zero_le ys.length,
        Nat.zero_le ((4 * (b.queryBound + factor n rest + 40)) * (xs.length + ys.length))]
    · dsimp only
      have hf := factor_ge (b :: rest)
      nlinarith only [hf, Nat.zero_le xs.length, Nat.zero_le ys.length]

private theorem factor_add (blocks : List (Block n g)) (Q : ℕ)
    (hQ : ∀ b ∈ blocks, b.queryBound ≤ Q) :
    factor n blocks + (2 * Q + 60) ≤
      4 ^ blocks.length * (64 * (n + 1) + 5 + (2 * Q + 60)) := by
  induction blocks with
  | nil => simp [factor]
  | cons b rest ih =>
    have hb := hQ b (by simp)
    have hr := ih (fun c hc => hQ c (by simp [hc]))
    simp only [factor, List.length_cons, pow_succ]
    nlinarith only [hb, hr, Nat.zero_le Q]

theorem factor_scale (I : Instance n) (hn : 10000 ≤ n)
    (blocks : List (Block n g)) (hlen : blocks.length = 4)
    (hg : g ≤ n) (hs : ∀ b ∈ blocks, b.steps ≤ n + 4) :
    factor n blocks ≤ inputScale I ^ 5 := by
  have hf := factor_add blocks (128 * (n + 1) ^ 3)
    (fun b hb => PreparedSeparatorWork.queryBound b hg (hs b hb))
  rw [hlen] at hf
  have hlin : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by decide) (n + 1)
  have hone : 1 ≤ (n + 1) ^ 3 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ n + 1 by omega) 3
  have hsmall : factor n blocks ≤ 131072 * (n + 1) ^ 3 := by
    norm_num at hf
    nlinarith only [hf, hlin, hone]
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 131072 ≤ inputScale I ^ 2 := by nlinarith only [hu, hn]
  calc
    factor n blocks ≤ 131072 * (n + 1) ^ 3 := hsmall
    _ ≤ inputScale I ^ 2 * inputScale I ^ 3 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left hu 3)
    _ = inputScale I ^ 5 := by ring

end LowSpaceSubsetSum.BudgetedSeparatorCheck

end OAI
