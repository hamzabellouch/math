import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseCandidateWork
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialScalar

namespace OAI

namespace EditApproximation
open Filter
namespace BinaryFraction

/-- All actual initial-estimator branches have the same source-width charging
form. In the long-target branch no target scan or root is executed. -/
theorem computedCoarseInitialWithWork_bound :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N →
      (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws).2 ≤
        inputHeight N ^ 36 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N)
          x y draws + x.length + 1) := by
  filter_upwards [computedCoarseCandidate_bounds, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hcandidate hN hell
  intro B d x y hBdef hddef hsize hsymbols hB hq hL draws
  let H := inputHeight N
  change (coarseInitialWithWork (H ^ 4) (64 * H) N hB hq hL x y draws).2 ≤
    H ^ 36 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws + x.length + 1)
  have hH : 100 ≤ H := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hlength : Nat.size N ≤ H + 1 :=
    (Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N)
  have hxlen : x.length ≤ N := (le_max_left _ _).trans hsize
  have hylen : y.length ≤ N := (le_max_right _ _).trans hsize
  have hx : Nat.size x.length ≤ H + 1 := (Nat.size_le_size hxlen).trans hlength
  have hy : Nat.size y.length ≤ H + 1 := (Nat.size_le_size hylen).trans hlength
  have hlongcost : (binaryNaturalCompareWithWork (2 * x.length) y.length).2 ≤ 8 * H + 17 := by
    have hc := binaryNaturalCompareWithWork_cost (2 * x.length) y.length
    have hp := natural_product_bit_length 2 x.length
    rw [show Nat.size 2 = 2 by decide] at hp
    omega
  have hpow36 : 100 * H ^ 3 ≤ H ^ 36 := by
    have hh := Nat.mul_le_mul_right (H ^ 3) hH
    have hp := Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 4 ≤ 36)
    nlinarith only [hh, hp]
  have hH3 : H ≤ H ^ 3 := Nat.le_pow (by decide)
  have hmul := Nat.mul_le_mul_left (H ^ 36)
    (show 1 ≤ coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws +
      x.length + 1 by omega)
  by_cases hlong : 2 * x.length < y.length
  · have hb := (binaryNaturalCompareWithWork_lt (2 * x.length) y.length).mpr hlong
    change (coarseInitialWithWork _ _ _ _ _ _ _ _ _).2 ≤ _
    simp only [coarseInitialWithWork, hb, ite_true]
    nlinarith only [hlongcost, hlength, hy, hH, hpow36, hmul, hH3]
  have hb : ¬ (binaryNaturalCompareWithWork (2 * x.length) y.length).1 = Ordering.lt :=
    fun h => hlong ((binaryNaturalCompareWithWork_lt _ _).mp h)
  by_cases he : x = y
  · have heq := (naturalListEqualWithWork_value x y).mpr he
    have hc := naturalListEqualWithWork_cost x y (H ^ 3) hsymbols
    have hsource : y.length = x.length := congrArg List.length he.symm
    have hf : (2 * x.length + 1) * (8 * H ^ 3 + 4) + (8 * H + 17) + 3 ≤
        H ^ 36 * (x.length + 1) := by
      have ha := Nat.mul_le_mul_right (x.length + 1) hpow36
      have h3 : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
      nlinarith only [ha, hH, h3, hH3]
    simp only [coarseInitialWithWork, ite_eq_right hb, heq, ite_true]
    rw [hsource] at hc
    have hz : coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws = 0 := by
      simp only [coarseInitialArrayWork, ite_eq_right hlong, ite_eq_left he]
    rw [hz, zero_add]
    nlinarith only [hc, hf, hlongcost]
  have hclog : Nat.clog 2 (coarseEntryWidth x y) ≤ H :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
      (hsize.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have hN4 : Nat.size N ≤ H ^ 4 := by
    have hp2 : H + 1 ≤ H ^ 2 := by nlinarith
    have hp : H + 1 ≤ H ^ 4 := hp2.trans
      (Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 2 ≤ 4))
    exact hlength.trans hp
  have hw := coarseInitialWithWork_cost (inputHeight N ^ 4) (64 * inputHeight N) N
    (H ^ 4) (H ^ 3) hB hq hL x y draws (by
      have hp : H ≤ H ^ 4 := Nat.le_pow (by decide)
      omega) hN4
    ((Nat.size_le_size hxlen).trans hN4) ((Nat.size_le_size hylen).trans hN4) hsymbols
    (fun i => (hcandidate B d x y hBdef hddef hsize hB hq hL i (draws i)).1)
  let f := fun i : CoarseGuessIndex (coarseEntryWidth x y) =>
    (coarseCandidateWithWork (H ^ 4) (64 * H) hB hq hL x y i (draws i)).2
  have hsum : ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map f).sum =
      ∑ i, f i := by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have hr : ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map f).sum ≤
      H ^ 32 * (coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draws +
        (Nat.clog 2 (coarseEntryWidth x y) + 1)) := by
    rw [hsum]
    calc
      _ ≤ ∑ i : CoarseGuessIndex (coarseEntryWidth x y), H ^ 32 *
          (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i)
            (initialThresholdQ N) (initialLambda N) (coarseEntryTree B d x y) (draws i)
            (coarseGuess (coarseEntryWidth x y) i) + 1) :=
        Finset.sum_le_sum (fun i _ => (hcandidate B d x y hBdef hddef hsize hB hq hL i (draws i)).2)
      _ = _ := by
        simp only [coarseInitialArrayWork, ite_eq_right hlong, ite_eq_right he,
          ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one]
  have hscan : x.length + y.length + 1 ≤ 3 * x.length + 1 := by omega
  apply coarseInitial_aggregate_scalar H x.length _ (Nat.clog 2 (coarseEntryWidth x y) + 1)
    _ _ hH (by omega) hr
  exact hw.trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right (8 * H ^ 3 + 4) hscan) _) _)

end BinaryFraction
end EditApproximation

end OAI
