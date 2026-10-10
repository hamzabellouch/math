import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedDecisionRound
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparationWork
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilyWork
import OAI.Combinatorics.LowSpaceSubsetSum.Search.DecisionRepetition

namespace OAI

/-! # Every-outcome work of the concrete repeated decision procedure -/

namespace LowSpaceSubsetSum.PreparedDecisionWork

variable {n : ℕ}

theorem compression_setup (I : Instance n) (hn : 10000 ≤ n) :
    (n + 1) * n ^ 3 + SamplerExecution.primeTestBudget n +
      510 * (n + 1) ^ 2 + 6 ≤ inputScale I ^ 8 * 2 ^ ((n + 1) / 2) := by
  let u := inputScale I
  let H := 2 ^ ((n + 1) / 2)
  have hu : n + 1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hH : 1 ≤ H := Nat.one_le_two_pow
  have hn3 : n ^ 3 ≤ u ^ 3 := Nat.pow_le_pow_left (by omega) _
  have hu3 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right' (by omega) (by decide)
  have h4 : (n + 1) * n ^ 3 ≤ u ^ 4 := by
    simpa only [← pow_succ'] using Nat.mul_le_mul hu hn3
  have h4H : u ^ 4 ≤ u ^ 4 * H := Nat.le_mul_of_pos_right _ hH
  have hp : SamplerExecution.primeTestBudget n ≤ u ^ 4 * H :=
    Nat.mul_le_mul_right H (hn3.trans hu3)
  have h2 : (n + 1) ^ 2 ≤ u ^ 4 * H :=
    ((Nat.pow_le_pow_left hu 2).trans (pow_le_pow_right' (by omega) (by decide))).trans h4H
  have h1 : 1 ≤ u ^ 4 * H := (Nat.one_le_pow _ _ (by omega)).trans h4H
  have ht : (n + 1) * n ^ 3 + SamplerExecution.primeTestBudget n +
      510 * (n + 1) ^ 2 + 6 ≤ 518 * (u ^ 4 * H) := by
    omega
  have h518 : 518 ≤ u ^ 4 := by
    have h := pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 4)
    simp only [pow_one] at h
    omega
  apply ht.trans
  calc
    _ ≤ u ^ 4 * (u ^ 4 * H) := Nat.mul_le_mul_right _ h518
    _ = _ := by ring

theorem round (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (s : PreparedDecisionRound.Seed I hn) :
    (PreparedDecisionRound.run I hn hlog s).2 ≤
      inputScale I ^ 501 * 2 ^ ((n + 1) / 2) := by
  let T := trialWatchdog I
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have h8 : inputScale I ^ 8 * 2 ^ ((n + 1) / 2) ≤ T :=
    Nat.mul_le_mul_right _ (pow_le_pow_right' (by omega) (by decide))
  have h6 : inputScale I ^ 6 * 2 ^ ((n + 1) / 2) ≤ T :=
    Nat.mul_le_mul_right _ (pow_le_pow_right' (by omega) (by decide))
  have hc := SampledCompressionTrial.work (CompressionData.mk I) (by omega) s.1
  have hs := compression_setup I (by omega)
  have hc' : (SampledCompressionTrial.run (CompressionData.mk I) (by omega) s.1).2 ≤ 3 * T := by
    dsimp only [SampledCompressionTrial.allowance, CompressionFromPermutation.charge,
      CompressionData.mk] at hc
    omega
  have hr := RepresentationPreparedTrial.work I (by omega) hlog hscale s.2 (2 * T)
  have hp := (RepresentationPreparationWork.bounded I (by omega) hlog s.2.1).trans h8
  have hf := (RepresentationFamilyWork.bound I (by omega)).trans h6
  change 60 * RepresentationPreparedTrial.width n + 51 +
    44 * 2 ^ RepresentationPreparedTrial.width n *
      (RepresentationPreparedTrial.width n * n ^ 3 +
        32 * (RepresentationPreparedTrial.width n + 1) ^ 3 + 4) + 22 ≤ T at hf
  have hr' : (RepresentationPreparedTrial.run I (by omega) hlog s.2 (2 * T)).2 ≤ 4 * T + 18 := by
    omega
  have hT : 21 ≤ T := by
    have hpow : inputScale I ≤ inputScale I ^ 500 := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale I)
        (by decide : 1 ≤ 500)
    have hmul := Nat.le_mul_of_pos_right (inputScale I ^ 500)
      (Nat.one_le_two_pow (n := (n + 1) / 2))
    dsimp [T, trialWatchdog]
    omega
  have hsum : (PreparedDecisionRound.run I hn hlog s).2 ≤ 8 * T := by
    change (SampledCompressionTrial.run (CompressionData.mk I) (by omega) s.1).2 +
      (RepresentationPreparedTrial.run I (by omega) hlog s.2 (2 * T)).2 + 3 ≤ _
    omega
  apply hsum.trans
  change 8 * (inputScale I ^ 500 * 2 ^ ((n + 1) / 2)) ≤ _
  calc
    _ ≤ inputScale I * (inputScale I ^ 500 * 2 ^ ((n + 1) / 2)) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem repeated (I : Instance n) (hn : 180000000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (s : Fin (inputScale I ^ 120) → PreparedDecisionRound.Seed I hn) :
    (DecisionRepetition.run (PreparedDecisionRound.run I hn hlog) s).2 ≤
      inputScale I ^ 622 * 2 ^ ((n + 1) / 2) := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hH : 1 ≤ 2 ^ ((n+1)/2) := Nat.one_le_two_pow
  have hw := DecisionRepetition.work (PreparedDecisionRound.run I hn hlog) s
    _ (round I hn hlog hscale)
  have h1 : 1 ≤ inputScale I ^ 120 := Nat.one_le_pow _ _ (by omega)
  have hp : inputScale I ^ 120 ≤ inputScale I ^ 621 * 2 ^ ((n+1)/2) :=
    (pow_le_pow_right' (by omega) (by decide)).trans (Nat.le_mul_of_pos_right _ hH)
  have hsmall : 1 ≤ inputScale I ^ 621 * 2 ^ ((n+1)/2) := h1.trans hp
  have he : inputScale I ^ 120 * (inputScale I ^ 501 * 2 ^ ((n+1)/2)) =
      inputScale I ^ 621 * 2 ^ ((n+1)/2) := by
    rw [← Nat.mul_assoc, ← pow_add]
  have ht : (DecisionRepetition.run (PreparedDecisionRound.run I hn hlog) s).2 ≤
      3 * (inputScale I ^ 621 * 2 ^ ((n+1)/2)) := by
    nlinarith only [hw, hp, hsmall, he]
  apply ht.trans
  calc
    _ ≤ inputScale I * (inputScale I ^ 621 * 2 ^ ((n+1)/2)) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [← Nat.mul_assoc, ← pow_succ']

end LowSpaceSubsetSum.PreparedDecisionWork

end OAI
