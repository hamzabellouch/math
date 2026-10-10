import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseReadBudget
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedRootBound
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedInitialCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseInitialWork

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

attribute [local irreducible] coarseRootReadExtra coarseInitialReadExtra
  coarseIndexedInitialWithWork coarseInitialWithWork

theorem computedCoarseRootReadExtra_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d),
      coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i)
        (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y draws ≤
        inputHeight N ^ 32 * (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
          (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) draws
          (coarseGuess (coarseEntryWidth x y) i) + 1) := by
  filter_upwards [computedCoarseReadBudget, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hbudget hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL i draws
  let H := inputHeight N
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hc := coarseRootReadExtra_bound (coarseGuess (coarseEntryWidth x y) i)
    (H ^ 4) (64 * H) (H ^ 30) hB hq hL (one_le_pow₀ (by omega)) x y draws
    (hbudget B d x y hBdef hddef hsize hsymbol i)
  have hscale : 64 * H ^ 30 ≤ H ^ 32 := by
    calc
      _ ≤ H ^ 2 * H ^ 30 := Nat.mul_le_mul_right _ (by nlinarith only [hH])
      _ = _ := by rw [← pow_add]
  have hs := Nat.mul_le_mul_right
    (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i) (initialThresholdQ N)
      (initialLambda N) (coarseEntryTree B d x y) draws (coarseGuess (coarseEntryWidth x y) i) + 1) hscale
  simp only [H, initialThresholdQ, initialLambda, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hc hs ⊢
  nlinarith only [hc, hs]

theorem computedCoarseInitialReadExtra_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      coarseInitialReadExtra (inputHeight N ^ 4) (64 * inputHeight N) hB hq hL x y draws ≤
        inputHeight N ^ 34 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + 1) := by
  filter_upwards [computedCoarseRootReadExtra_bound, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hroot hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL draws
  let H := inputHeight N
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  unfold coarseInitialReadExtra
  split_ifs with hlong hequal
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · have hlong' : ¬ 2 * x.length < y.length :=
      fun h => hlong ((binaryNaturalCompareWithWork_lt _ _).mpr h)
    have hequal' : x ≠ y := fun h => hequal ((naturalListEqualWithWork_value x y).mpr h)
    have hclog : Nat.clog 2 (coarseEntryWidth x y) ≤ H :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
        (hsize.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
    have hsum : ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map fun i =>
        coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i) (inputHeight N ^ 4)
          (64 * inputHeight N) hB hq hL x y (draws i)).sum ≤
        H ^ 32 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + (Nat.clog 2 (coarseEntryWidth x y) + 1)) := by
      rw [← List.ofFn_eq_map, List.sum_ofFn]
      calc
        _ ≤ ∑ i : CoarseGuessIndex (coarseEntryWidth x y), H ^ 32 *
            (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
              (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) (draws i)
              (coarseGuess (coarseEntryWidth x y) i) + 1) :=
          Finset.sum_le_sum (fun i _ => hroot B d x y hBdef hddef hsize hsymbol hB hq hL i (draws i))
        _ = _ := by
          simp only [coarseInitialArrayWork, ite_eq_right hlong', ite_eq_right hequal',
            ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul, mul_one]
    have ha : coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws +
        (Nat.clog 2 (coarseEntryWidth x y) + 1) ≤
        H ^ 2 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + 1) := by
      have hs : H + 1 ≤ H ^ 2 := by nlinarith only [hH]
      have hm := Nat.mul_le_mul_right
        (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws)
        (show 1 ≤ H ^ 2 from one_le_pow₀ (by omega))
      nlinarith only [hs, hm, hclog]
    calc
      _ ≤ _ := hsum
      _ ≤ H ^ 32 * (H ^ 2 * (coarseInitialArrayWork B d (initialThresholdQ N)
        (initialLambda N) x y draws + 1)) := Nat.mul_le_mul_left _ ha
      _ = _ := by ring

theorem computedCoarseIndexedInitialWithWork_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseIndexedInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws).2 ≤
        inputHeight N ^ 40 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + x.length + 1) := by
  filter_upwards [computedCoarseInitialWithWork_bound, computedCoarseInitialReadExtra_bound,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)]
    with N hold hextra hN hell
  intro B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have h1 := hold B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have h2 := hextra B d x y hBdef hddef hsize hsymbol hB hq hL draws
  have hc := coarseIndexedInitialWithWork_cost_compare (inputHeight N ^ 4) (64 * inputHeight N)
    N hB hq hL x y draws
  let H := inputHeight N
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hp : H ^ 34 ≤ H ^ 36 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs : 2 * H ^ 36 ≤ H ^ 40 := by
    calc
      _ ≤ H ^ 4 * H ^ 36 := Nat.mul_le_mul_right _
        ((by omega : 2 ≤ H).trans (Nat.le_pow (by decide)))
      _ = _ := by rw [← pow_add]
  have hm := Nat.mul_le_mul_right
    (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + x.length + 1) hs
  have he := Nat.mul_le_mul hp
    (show coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + 1 ≤
      coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + x.length + 1 by omega)
  dsimp only [H] at hm he
  nlinarith only [h1, h2, hc, hm, he]

end BinaryFraction
end EditApproximation

end OAI
