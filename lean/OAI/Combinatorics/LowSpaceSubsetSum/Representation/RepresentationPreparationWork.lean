import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraPreparation

namespace OAI

/-! # All-outcome work of the complete stored prefix -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPreparationWork

variable {n : ℕ}

theorem beyond_prefix (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (RepresentationExtraPreparation.run I hn hlog s).2 ≤
      (RepresentationPrefixArrays.run (canonicalRepresentationData I) s.1.1.1).2 +
        4000 * (n + 1) ^ 2 + 7 * n ^ 3 + 4 * SamplerExecution.primeTestBudget n + 21 := by
  have he := RepresentationExtraPreparation.work I hn hlog s
  have hr := RepresentationResiduePreparation.work I hn hlog s.1
  have hp := RepresentationPrimePreparation.work I hn hlog s.1.1
  have hs := RepresentationStoredPreparation.work I s.1.1.1
  omega

theorem bounded (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (RepresentationExtraPreparation.run I hn hlog s).2 ≤
      inputScale I ^ 8 * 2 ^ ((n + 1) / 2) := by
  let u := inputScale I
  let H := 2 ^ ((n + 1) / 2)
  let V := u ^ 6 * H
  have hu : n + 1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hH : 1 ≤ H := Nat.one_le_two_pow
  have hm : mixerSize n ≤ n := by unfold mixerSize; omega
  have hmh : mixerSize n ≤ (n + 1) / 2 := by unfold mixerSize; omega
  have h2m : 2 ^ mixerSize n ≤ H := Nat.pow_le_pow_right (by decide) hmh
  have hp6 (k : ℕ) (hk : k ≤ 6) : u ^ k ≤ u ^ 6 := pow_le_pow_right' (by omega) hk
  have huv : u ^ 6 ≤ V := Nat.le_mul_of_pos_right _ hH
  have hu1 : u ≤ u ^ 6 := by simpa only [pow_one] using hp6 1 (by decide)
  have hn1 : n ≤ V := (show n ≤ u by omega).trans
    (hu1.trans huv)
  have hm1 : mixerSize n ≤ V := hm.trans hn1
  have hn3 : n ^ 3 ≤ u ^ 6 := (Nat.pow_le_pow_left (show n ≤ u by omega) 3).trans (hp6 3 (by decide))
  have hn3v := hn3.trans huv
  have hn4 : n * n ^ 3 ≤ V := by
    have hh := Nat.mul_le_mul (show n ≤ u by omega) (Nat.pow_le_pow_left (show n ≤ u by omega) 3)
    calc
      _ ≤ u * u ^ 3 := hh
      _ = u ^ 4 := (pow_succ' _ _).symm
      _ ≤ V := (hp6 4 (by decide)).trans huv
  have hm4 : mixerSize n * n ^ 3 ≤ V := (Nat.mul_le_mul_right _ hm).trans hn4
  have hn2 : (n + 1) ^ 2 ≤ V := (Nat.pow_le_pow_left hu 2).trans ((hp6 2 (by decide)).trans huv)
  have hm2 : (mixerSize n + 1) ^ 2 ≤ V :=
    (Nat.pow_le_pow_left (by omega : mixerSize n + 1 ≤ n + 1) 2).trans hn2
  have h1 : 1 ≤ V := (Nat.one_le_pow _ _ (by omega)).trans huv
  have hp : SamplerExecution.primeTestBudget n ≤ V := by
    exact Nat.mul_le_mul_right H hn3
  have hmix : inputScale (canonicalRepresentationData I).input ^ 6 * 2 ^ mixerSize n ≤ V :=
    Nat.mul_le_mul_left (u ^ 6) h2m
  have hw := RepresentationPrefixArrays.work (canonicalRepresentationData I) hn s.1.1.1
  have hb := beyond_prefix I hn hlog s
  have htotal : (RepresentationExtraPreparation.run I hn hlog s).2 ≤ 5000 * V := by
    nlinarith only [hw, hb, hn1, hm1, hn3v, hn4, hm4, hn2, hm2, h1, hp, hmix]
  have hu2 : 5000 ≤ u ^ 2 := by nlinarith only [hu0]
  have hf : 5000 * u ^ 6 ≤ u ^ 8 := by
    calc
      _ ≤ u ^ 2 * u ^ 6 := Nat.mul_le_mul_right _ hu2
      _ = _ := by ring
  apply htotal.trans
  change 5000 * (u ^ 6 * H) ≤ u ^ 8 * H
  nlinarith only [Nat.mul_le_mul_right H hf]

end LowSpaceSubsetSum.RepresentationPreparationWork

end

end OAI
