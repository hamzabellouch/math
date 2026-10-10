import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayStorage
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarsePolynomial

namespace OAI

namespace EditApproximation
namespace BinaryFraction
open Filter

theorem computedCoarseRootArray_storage :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      coarseArrayStorage (coarseIndexedRootArray (coarseGuess (coarseEntryWidth x y) i)
        (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y draws) ≤
        1 + (2 * coarseGuess (coarseEntryWidth x y) i + 1) * (2 * inputHeight N ^ 3 + 3) := by
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
  rw [coarseIndexedRootArray_eq]
  exact coarseRootArray_storage k (H ^ 4) (64 * H) N (10 * H ^ 2) (H ^ 3)
    hB hq hL _ _ draws 0 hBbits hqbits hLbits hNbits hden hbound htree

theorem coarseRootArrayStorage_polynomial_scalar (N k : ℕ) (hk : k ≤ 2 * (N + 2)) :
    1 + (2 * k + 1) * (2 * inputHeight N ^ 3 + 3) ≤ (N + 2) ^ 20 := by
  let X := N + 2
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hH := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hH
  change inputHeight N ^ 3 ≤ X ^ 12 at hH
  have hone : 1 ≤ X ^ 12 := one_le_pow₀ (by omega)
  have hm : (2 * k + 1) * (2 * inputHeight N ^ 3 + 3) ≤ (5 * X) * (5 * X ^ 12) :=
    Nat.mul_le_mul (by dsimp only [X]; omega) (by omega)
  have hp : 1 ≤ X ^ 13 := one_le_pow₀ (by omega)
  have hc : 26 ≤ X ^ 7 := (by decide : 26 ≤ (2 : ℕ) ^ 7).trans (Nat.pow_le_pow_left hX 7)
  calc
    _ ≤ 26 * X ^ 13 := by nlinarith only [hm, hp]
    _ ≤ X ^ 7 * X ^ 13 := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add]

/-- Even retaining the final array from every candidate uses polynomial
space; the implementation may release each array after its root lookup. -/
theorem computedCoarseAllRootArrays_storage :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (∑ i : CoarseGuessIndex (coarseEntryWidth x y),
        coarseArrayStorage (coarseIndexedRootArray (coarseGuess (coarseEntryWidth x y) i)
          (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y (draws i))) ≤
        (N + 2) ^ 25 := by
  filter_upwards [computedCoarseRootArray_storage] with N hroot
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
    _ ≤ ∑ _i : CoarseGuessIndex (coarseEntryWidth x y), (N + 2) ^ 20 := by
      apply Finset.sum_le_sum
      intro i _
      exact (hroot B d x y hBdef hddef hsize hB hq hL i (draws i)).trans
        (coarseRootArrayStorage_polynomial_scalar N _ ((coarseGuess_le _ i).trans (by omega)))
    _ = (Nat.clog 2 (coarseEntryWidth x y) + 1) * (N + 2) ^ 20 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ (N + 2) ^ 5 * (N + 2) ^ 20 := Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [← pow_add]

end BinaryFraction
end EditApproximation

end OAI
