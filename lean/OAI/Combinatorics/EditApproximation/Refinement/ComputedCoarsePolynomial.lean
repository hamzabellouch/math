import OAI.Combinatorics.EditApproximation.Coarse.CoarseCompletePolynomial
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseIndexedWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRetainedValues

namespace OAI

namespace EditApproximation
namespace BinaryFraction
open Filter

theorem computedCoarseBranching_polynomial (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) : (integerParameters N).B ≤ (N + 2) ^ 4 := by
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  calc
    _ ≤ 2 ^ inputHeight N := computed_coarse_B_upper N hN hell
    _ ≤ 4 * (N + 2) ^ 2 := two_pow_inputHeight_le N
    _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add]

/-- A deterministic bound holds for every pruning outcome, including the
outcomes outside the accuracy event. -/
theorem computedCoarseInitialArrayWork_polynomial (N B d : ℕ) (x y : List ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hBdef : B = (integerParameters N).B)
    (hddef : d = computedCoarseDepth N (coarseEntryWidth x y))
    (hsize : coarseEntryWidth x y ≤ N)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws ≤
      (N + 2) ^ 19 := by
  have hB : 2 ≤ B := by
    have h := computed_coarse_branching N hN hell
    omega
  have hBP : B ≤ (N + 2) ^ 4 := by
    rw [hBdef]
    exact computedCoarseBranching_polynomial N hN hell
  have hd : d = intervalTreeDepth B (coarseEntryWidth x y) := by
    simp only [hddef, computedCoarseDepth, intervalTreeDepth, hBdef]
  have heach (i : CoarseGuessIndex (coarseEntryWidth x y)) :
      coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
        (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y)
        (draws i) (coarseGuess (coarseEntryWidth x y) i) ≤ (N + 2) ^ 14 := by
    have hk : coarseGuess (coarseEntryWidth x y) i ≤ 2 * (N + 2) :=
      (coarseGuess_le _ i).trans (by omega)
    rcases hd with rfl
    exact coarseActiveArrayWork_polynomial N B (coarseEntryWidth x y) _ _ _ _
      hB hsize hBP hk _ _
  have hclog : Nat.clog 2 (coarseEntryWidth x y) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
      (hsize.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have hcount : Nat.clog 2 (coarseEntryWidth x y) + 1 ≤ (N + 2) ^ 5 := by
    have hh := computed_height_polynomial N
    have hp : 1 ≤ (N + 2) ^ 4 := one_le_pow₀ (by omega)
    have hm := Nat.mul_le_mul_right ((N + 2) ^ 4) (show 2 ≤ N + 2 by omega)
    nlinarith only [hclog, hh, hp, hm]
  unfold coarseInitialArrayWork
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · calc
      _ ≤ ∑ _i : CoarseGuessIndex (coarseEntryWidth x y), (N + 2) ^ 14 :=
        Finset.sum_le_sum (fun i _ => heach i)
      _ = (Nat.clog 2 (coarseEntryWidth x y) + 1) * (N + 2) ^ 14 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ (N + 2) ^ 5 * (N + 2) ^ 14 := Nat.mul_le_mul_right _ hcount
      _ = _ := by rw [← pow_add]

/-- The counted indexed implementation has polynomial work on every draw. -/
theorem computedCoarseIndexedInitialWithWork_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseIndexedInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N
        hB hq hL x y draws).2 ≤ (N + 2) ^ 180 := by
  filter_upwards [computedCoarseIndexedInitialWithWork_bound, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hwork hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have hw := hwork B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have ha := computedCoarseInitialArrayWork_polynomial N B d x y (by omega) hell
    hBdef hddef hsize draws
  have hx : x.length + 1 ≤ N + 2 := by
    have h := (le_max_left x.length y.length).trans hsize
    omega
  have hp : N + 2 ≤ (N + 2) ^ 19 := Nat.le_pow (by decide)
  have hm := Nat.mul_le_mul_right ((N + 2) ^ 19) (show 2 ≤ N + 2 by omega)
  have hsum : coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
      x y draws + x.length + 1 ≤ (N + 2) ^ 20 := by
    nlinarith only [ha, hx, hp, hm]
  have hh := Nat.pow_le_pow_left (computed_height_polynomial N) 40
  rw [← pow_mul] at hh
  calc
    _ ≤ _ := hw
    _ ≤ (N + 2) ^ 160 * (N + 2) ^ 20 := Nat.mul_le_mul hh hsum
    _ = _ := by rw [← pow_add]

end BinaryFraction
end EditApproximation

end OAI
