import OAI.Combinatorics.EditApproximation.Coarse.CoarseRootHistory
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseArrayStorage

namespace OAI

namespace EditApproximation
namespace BinaryFraction
open Filter

theorem computedCoarseRootHistory_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      coarseRootArrayHistory (coarseGuess (coarseEntryWidth x y) i)
        (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL
        (coarseTargetFrame (coarseGuess (coarseEntryWidth x y) i)
          (coarsePadTo (coarseEntryWidth x y) y)) (coarseEntryTree B d x y) draws 0 ≤
        (32 * (inputHeight N ^ 3 + 1)) *
          ((B * (2 * coarseGuess (coarseEntryWidth x y) i + 1) + 1) * coarseCompleteNodes B d) := by
  filter_upwards [computedCoarse_bitParameters, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hbits hN hell
  intro B d x y hBdef hddef hsize hB hq hL i draws
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  have hk : k ≤ 2 * (N + 2) := (coarseGuess_le _ i).trans (by omega)
  obtain ⟨hden, hbound, hBbits, hqbits, hLbits, hNbits, _hD⟩ :=
    hbits B d (coarseEntryWidth x y) k hBdef hddef hsize hk
  have hcap : coarseEntryWidth x y ≤ B ^ d := by
    rw [hBdef, hddef]
    exact (computed_coarse_depth N _ (by omega) hsize hell).1
  have htree : 0 + (coarseEntryTree B d x y).word.length ≤ N := by
    rw [coarseEntryTree_word B d x y hcap, coarsePadTo_length _ _ (le_max_left _ _)]
    simpa only [Nat.zero_add] using hsize
  exact coarseRootArrayHistory_bound k (H ^ 4) (64 * H) N (10 * H ^ 2) (H ^ 3)
    hB hq hL _ _ draws 0 hBbits hqbits hLbits hNbits hden hbound htree

theorem computedCoarseRootHistory_polynomial (N B d k n : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hBdef : B = (integerParameters N).B) (hddef : d = computedCoarseDepth N n)
    (hn : n ≤ N) (hk : k ≤ 2 * (N + 2)) :
    (32 * (inputHeight N ^ 3 + 1)) *
      ((B * (2 * k + 1) + 1) * coarseCompleteNodes B d) ≤ (N + 2) ^ 32 := by
  let X := N + 2
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hH := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hH
  change inputHeight N ^ 3 ≤ X ^ 12 at hH
  have hone : 1 ≤ X ^ 12 := one_le_pow₀ (by omega)
  have hc : 64 ≤ X ^ 6 := (by decide : 64 ≤ (2 : ℕ) ^ 6).trans (Nat.pow_le_pow_left hX 6)
  have hu : 32 * (inputHeight N ^ 3 + 1) ≤ X ^ 18 := by
    calc
      _ ≤ 64 * X ^ 12 := by omega
      _ ≤ X ^ 6 * X ^ 12 := Nat.mul_le_mul_right _ hc
      _ = _ := by rw [← pow_add]
  have hB : 2 ≤ B := by
    have h := computed_coarse_branching N hN hell
    omega
  have hBP : B ≤ (N + 2) ^ 4 := by
    rw [hBdef]
    exact computedCoarseBranching_polynomial N hN hell
  have hd : d = intervalTreeDepth B n := by
    simp only [hddef, computedCoarseDepth, intervalTreeDepth, hBdef]
  have hnodes := coarseCompleteNodes_polynomial N B n hB hn hBP
  rw [← hd] at hnodes
  have hw := coarseRootWidth_polynomial N B k hBP hk
  calc
    _ ≤ X ^ 18 * (X ^ 8 * X ^ 6) := Nat.mul_le_mul hu (Nat.mul_le_mul hw hnodes)
    _ = _ := by ring

/-- Total stored bits of all recursive array results from all guesses.
This bound holds for every draw, without a successful-approximation premise. -/
theorem computedCoarseAllHistories_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (∑ i : CoarseGuessIndex (coarseEntryWidth x y),
        coarseRootArrayHistory (coarseGuess (coarseEntryWidth x y) i)
          (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL
          (coarseTargetFrame (coarseGuess (coarseEntryWidth x y) i)
            (coarsePadTo (coarseEntryWidth x y) y)) (coarseEntryTree B d x y) (draws i) 0) ≤
        (N + 2) ^ 37 := by
  filter_upwards [computedCoarseRootHistory_bound, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hroot hN hell
  intro B d x y hBdef hddef hsize hB hq hL draws
  have hclog : Nat.clog 2 (coarseEntryWidth x y) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
      (hsize.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have hcount : Nat.clog 2 (coarseEntryWidth x y) + 1 ≤ (N + 2) ^ 5 := by
    have hh := computed_height_polynomial N
    have hp : 1 ≤ (N + 2) ^ 4 := one_le_pow₀ (by omega)
    have hm := Nat.mul_le_mul_right ((N + 2) ^ 4) (show 2 ≤ N + 2 by omega)
    nlinarith only [hclog, hh, hp, hm]
  calc
    _ ≤ ∑ _i : CoarseGuessIndex (coarseEntryWidth x y), (N + 2) ^ 32 := by
      apply Finset.sum_le_sum
      intro i _
      exact (hroot B d x y hBdef hddef hsize hB hq hL i (draws i)).trans
        (computedCoarseRootHistory_polynomial N B d _ (coarseEntryWidth x y)
          (by omega) hell hBdef hddef hsize ((coarseGuess_le _ i).trans (by omega)))
    _ = (Nat.clog 2 (coarseEntryWidth x y) + 1) * (N + 2) ^ 32 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ (N + 2) ^ 5 * (N + 2) ^ 32 := Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [← pow_add]

end BinaryFraction
end EditApproximation

end OAI
