import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseBitParameters
import OAI.Combinatorics.EditApproximation.Coarse.CoarseNumericalUnit
import OAI.Combinatorics.EditApproximation.Coarse.CoarseRootBounds
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialCost

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

theorem coarseGuess_le (n : ℕ) (i : CoarseGuessIndex n) : coarseGuess n i ≤ 2 * (n + 1) := by
  have hi : i.val ≤ Nat.clog 2 n := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hi
  by_cases hn : n = 0
  · subst n
    simp only [Nat.clog_zero_right, pow_zero] at hp
    exact hp.trans (by decide)
  · have hr := (rejectionWord_range n (by omega)).2
    unfold rejectionBitCount at hr
    exact hp.trans (by omega)

private theorem coarseCandidate_scalar (H a root add mul size : ℕ) (hH : 100 ≤ H)
    (hr : root ≤ H ^ 30 * (2 * a + 1))
    (ha : add ≤ 6000 * (H ^ 3 + 1) ^ 2)
    (hm : mul ≤ 2000 * (8 * H ^ 3 + 7) ^ 2) (hs : size ≤ H ^ 3) :
    root + add + mul + size + 3 ≤ H ^ 32 * (a + 1) := by
  have ht : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
  have hb : add + mul + size + 3 ≤ 1000000 * H ^ 6 := by
    nlinarith only [ha, hm, hs, ht]
  have hc : 1000000 ≤ H ^ 4 := by
    have h := Nat.pow_le_pow_left hH 4
    norm_num at h
    omega
  have hbig : 1000000 * H ^ 6 ≤ H ^ 10 := by
    calc
      _ ≤ H ^ 4 * H ^ 6 := Nat.mul_le_mul_right _ hc
      _ = _ := by rw [← pow_add]
  have hexp : H ^ 10 ≤ H ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
  have htwo : 2 * H ^ 30 ≤ H ^ 32 := by
    have hh : 2 ≤ H ^ 2 := by nlinarith
    have hz := Nat.mul_le_mul_left (H ^ 30) hh
    simpa only [← pow_add, Nat.mul_comm] using hz
  nlinarith only [hr, hb, hbig, hexp, Nat.mul_le_mul_right (a + 1) htwo]

theorem computedCoarseRoot_for_candidate :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4)
      (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      let k := coarseGuess (coarseEntryWidth x y) i
      let root := coarseRootWithWork k (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
      root.1.width ≤ inputHeight N ^ 3 ∧
      root.2 ≤ inputHeight N ^ 30 * (2 * coarseActiveArrayWork k
        (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws k + 1) := by
  filter_upwards [computedCoarse_bitParameters, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hbits hN hell
  intro B d x y hBdef hddef hsize hB hq hL i draws
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  let frame := coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y)
  let tree := coarseEntryTree B d x y
  let root := coarseRootWithWork k (H ^ 4) (64 * H) hB hq hL frame tree draws 0 (coarseRootShift k)
  have hH : 100 ≤ H := by
    exact (by decide : 100 ≤ 256).trans
      (computed_coarse_height_large N (by omega) hell)
  have hk : k ≤ 2 * (N + 2) :=
    (coarseGuess_le _ i).trans (by omega)
  obtain ⟨hden, hbound, hBbits, hqbits, hLbits, hNbits, hD⟩ :=
    hbits B d (coarseEntryWidth x y) k hBdef hddef hsize hk
  have hcap : coarseEntryWidth x y ≤ B ^ d := by
    rw [hBdef, hddef]
    exact (computed_coarse_depth N _ (by omega) hsize hell).1
  have htree : 0 + tree.word.length ≤ N := by
    dsimp only [tree]
    rw [coarseEntryTree_word B d x y hcap, coarsePadTo_length _ _ (le_max_left _ _)]
    simpa only [Nat.zero_add] using hsize
  have hdepth : d ≤ H := hddef.symm ▸ (computed_coarse_depth N _ (by omega) hsize hell).2
  have hrw : root.1.width ≤ H ^ 3 :=
    coarseRootWithWork_width k (H ^ 4) (64 * H) N (10 * H ^ 2) (H ^ 3)
      hB hq hL frame tree draws 0 (coarseRootShift k)
      hBbits hqbits hLbits hNbits hden hbound htree
  have hrc := coarseRootWithWork_height_bound k (H ^ 4) (64 * H) N (10 * H ^ 2) H
    hB hq hL frame tree draws 0 (coarseRootShift k)
    hBbits hqbits hLbits hNbits hden hD hdepth hbound htree
  have hrc' : root.2 ≤ H ^ 30 *
      (2 * coarseActiveArrayWork k (initialThresholdQ N) (initialLambda N) tree draws k + 1) := by
    have hc := hrc.trans (Nat.mul_le_mul_right _ (coarseNumericalUnit_le_power H (by omega)))
    simpa only [initialThresholdQ, initialLambda, H, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hc
  exact ⟨hrw, hrc'⟩

private theorem coarseCandidate_k_bits (N k B d : ℕ)
    (hb : Nat.size (coarseLevelMagnitude N k B d + 2) +
      2 * (10 * inputHeight N ^ 2) + 1 ≤ inputHeight N ^ 3) :
    Nat.size k + 2 ≤ inputHeight N ^ 3 := by
  have h := Nat.size_le_size (coarseLevelMagnitude_ge N k B d)
  have h' := Nat.size_le_size (show coarseLevelMagnitude N k B d ≤
    coarseLevelMagnitude N k B d + 2 by omega)
  have hh : 0 < inputHeight N := Nat.two_pow_pos _
  have hdpos : 0 < 10 * inputHeight N ^ 2 := by positivity
  omega

/-- Every executed dyadic candidate has a short binary value and its complete
arithmetic cost is bounded by a fixed height power times its active-array work. -/
theorem computedCoarseCandidate_bounds :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4)
      (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      (coarseCandidateWithWork (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y i draws).1.width ≤
        inputHeight N ^ 4 ∧
      (coarseCandidateWithWork (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y i draws).2 ≤
        inputHeight N ^ 32 * (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
          (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws
          (coarseGuess (coarseEntryWidth x y) i) + 1) := by
  filter_upwards [computedCoarseRoot_for_candidate, computedCoarse_bitParameters,
    eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hroot hbits hN hell
  intro B d x y hBdef hddef hsize hB hq hL i draws
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseRootWithWork k (H ^ 4) (64 * H) hB hq hL
    (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
    (coarseEntryTree B d x y) draws 0 (coarseRootShift k)
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  obtain ⟨hrw, hrc'⟩ := hroot B d x y hBdef hddef hsize hB hq hL i draws
  change root.1.width ≤ H ^ 3 at hrw
  change root.2 ≤ H ^ 30 * (2 * coarseActiveArrayWork k
    (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws k + 1) at hrc'
  have hk : k ≤ 2 * (N + 2) := (coarseGuess_le _ i).trans (by omega)
  have hbound := (hbits B d (coarseEntryWidth x y) k hBdef hddef hsize hk).2.1
  have hkw : Nat.size k + 2 ≤ H ^ 3 := coarseCandidate_k_bits N k B d hbound
  have hnw : (nat k).width ≤ H ^ 3 := (nat_width_le k).trans hkw
  have hsw := canonicalAddWithWork_width root.1 (nat k) (H ^ 3) hrw hnw
  have hsc := canonicalAddWithWork_cost root.1 (nat k) (H ^ 3) hrw hnw
  have htw : (nat 2).width ≤ 8 * H ^ 3 + 6 := (nat_width_le 2).trans (by rw [show Nat.size 2 = 2 by decide]; omega)
  have hmw := canonicalMulWithWork_width (nat 2) (canonicalAddWithWork root.1 (nat k)).1
    (8 * H ^ 3 + 6) htw hsw
  have hmc := canonicalMulWithWork_cost (nat 2) (canonicalAddWithWork root.1 (nat k)).1
    (8 * H ^ 3 + 6) htw hsw
  constructor
  · change (canonicalMulWithWork (nat 2) (canonicalAddWithWork root.1 (nat k)).1).1.width ≤ H ^ 4
    have hh := Nat.mul_le_mul_right (H ^ 3) hH
    have ht : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
    nlinarith only [hmw, hh, ht]
  · change root.2 + (canonicalAddWithWork root.1 (nat k)).2 +
      (canonicalMulWithWork (nat 2) (canonicalAddWithWork root.1 (nat k)).1).2 + Nat.size k + 3 ≤ _
    exact coarseCandidate_scalar H _ _ _ _ _ hH hrc' hsc hmc (by omega)

end BinaryFraction
end EditApproximation

end OAI
