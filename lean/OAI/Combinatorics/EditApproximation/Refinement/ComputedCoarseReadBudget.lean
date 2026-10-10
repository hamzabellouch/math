import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseCandidateWork

namespace OAI

namespace EditApproximation
open Filter

/-- Every descriptor, stored-symbol comparison and frame operation used by a
computed coarse root has a uniform fixed-power bit budget. -/
theorem computedCoarseReadBudget :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ i : CoarseGuessIndex (coarseEntryWidth x y),
      CoarseReadBudget B d (coarseGuess (coarseEntryWidth x y) i) (coarseEntryWidth x y)
        x y (inputHeight N ^ 30) := by
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  intro B d x y hBdef hddef hsize hsymbol i
  let H := inputHeight N
  let k := coarseGuess (coarseEntryWidth x y) i
  have hH : 256 ≤ H := computed_coarse_height_large N (by omega) hell
  have hdepth : d ≤ H := hddef.symm ▸ (computed_coarse_depth N _ (by omega) hsize hell).2
  have hBpos : 1 ≤ B := by
    rw [hBdef]
    change 1 ≤ inputHeight N ^ coarseExponent (inputSmallLog N)
    exact one_le_pow₀ (Nat.succ_le_of_lt (Nat.two_pow_pos _))
  have hb : Nat.size B ≤ 2 * H := by
    have h := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
    rw [← hBdef] at h
    simp only [Nat.size_pow] at h
    exact h.trans (by dsimp only [H]; omega)
  have hcube : 100 * H ^ 2 ≤ H ^ 3 := by
    have h := Nat.mul_le_mul_right (H ^ 2) (show 100 ≤ H by omega)
    nlinarith only [h]
  have hp : Nat.size (B ^ d) ≤ H ^ 3 := by
    have h := natural_power_bit_length B d
    have hh := Nat.mul_le_mul hdepth hb
    have hsq := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
    nlinarith only [h, hh, hsq, hH]
  have hn : Nat.size (coarseEntryWidth x y) ≤ H ^ 3 := by
    have h := (Nat.size_le_size hsize).trans
      ((Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N))
    change Nat.size (coarseEntryWidth x y) ≤ H + 1 at h
    have hpow : H ≤ H ^ 3 := Nat.le_pow (by decide)
    have hsq := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
    nlinarith only [h, hpow, hsq, hH, hcube]
  have hk : Nat.size (2 * k + 1) ≤ H ^ 3 := by
    have hkn : k ≤ 2 * (N + 2) := (BinaryFraction.coarseGuess_le _ i).trans (by omega)
    have hks := (Nat.size_le_size hkn).trans (natural_product_bit_length 2 (N + 2))
    have hn' := inputLength_register_word N
    change Nat.size (N + 2) ≤ H + 1 at hn'
    have hs := natural_sum_bit_length (2 * k) 1
    have hm := natural_product_bit_length 2 k
    norm_num only [show Nat.size 2 = 2 by decide, show Nat.size 1 = 1 by decide] at hks hs hm
    have hsq := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
    nlinarith only [hks, hn', hs, hm, hsq, hH, hcube]
  exact coarseReadBudget_height B d k (coarseEntryWidth x y) H x y (by omega) hdepth hBpos
    (by have hpow : H ≤ H ^ 2 := Nat.le_pow (by decide); nlinarith only [hb, hpow, hH, hcube]) hp hn hk hsymbol

end EditApproximation

end OAI
