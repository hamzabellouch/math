import OAI.Combinatorics.EditApproximation.Coarse.CoarseBitParameters
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseBits

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

 theorem computedCoarse_bitParameters :
    ∀ᶠ N : ℕ in atTop, ∀ B d n k : ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N n → n ≤ N → k ≤ 2 * (N + 2) →
      Nat.size (coarseCommonDenominator 1 (inputHeight N ^ 4) (64 * inputHeight N) B d) ≤
        10 * inputHeight N ^ 2 ∧
      Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * (10 * inputHeight N ^ 2) + 1 ≤ inputHeight N ^ 3 ∧
      Nat.size B + 2 ≤ inputHeight N ^ 3 ∧
      Nat.size (inputHeight N ^ 4) + 2 ≤ inputHeight N ^ 3 ∧
      Nat.size (64 * inputHeight N) + 2 ≤ inputHeight N ^ 3 ∧
      Nat.size N + 2 ≤ inputHeight N ^ 3 ∧
      10 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
  filter_upwards [computedParameterPower_word, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hpower hN hell
  intro B d n k hBdef hddef hn hk
  have hH := computed_coarse_height_large N (by omega) hell
  have hD : d ≤ inputHeight N := hddef.symm ▸ (computed_coarse_depth N n (by omega) hn hell).2
  have hb : Nat.size B ≤ 2 * inputHeight N := by
    have hb' := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
    simp only [Nat.size_pow] at hb'
    rw [hBdef]
    omega
  have hq : Nat.size (inputHeight N ^ 4) ≤ 2 * inputHeight N := by
    have h := hpower 4 (by omega)
    omega
  have hHsize : Nat.size (inputHeight N) ≤ inputHeight N :=
    Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))
  have hL : Nat.size (64 * inputHeight N) ≤ 2 * inputHeight N := by
    have h := natural_product_bit_length 64 (inputHeight N)
    rw [show Nat.size 64 = 7 by decide] at h
    omega
  have hnsize : Nat.size N ≤ 2 * inputHeight N := by
    have h := (Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N)
    omega
  have hksize : Nat.size k ≤ 2 * inputHeight N := by
    have h := (Nat.size_le_size hk).trans (natural_product_bit_length 2 (N + 2))
    have hn' := inputLength_register_word N
    rw [show Nat.size 2 = 2 by decide] at h
    omega
  have hgrid := coarseBitParameters_grid (inputHeight N) N k B (inputHeight N ^ 4)
    (64 * inputHeight N) d (by omega) hD hnsize hksize hb hq hL
  have hcube : 100 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
    have h := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 100 ≤ inputHeight N by omega)
    nlinarith only [h]
  have hsquare : inputHeight N ≤ inputHeight N ^ 2 := Nat.le_pow (by decide)
  exact ⟨hgrid.1, hgrid.2, by nlinarith only [hb, hcube, hsquare, hH],
    by nlinarith only [hq, hcube, hsquare, hH], by nlinarith only [hL, hcube, hsquare, hH],
    by nlinarith only [hnsize, hcube, hsquare, hH], by nlinarith only [hcube]⟩

end BinaryFraction
end EditApproximation

end OAI
