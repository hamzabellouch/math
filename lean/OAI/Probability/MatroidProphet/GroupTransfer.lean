import OAI.Probability.MatroidProphet.Residual.Global
import OAI.Probability.MatroidProphet.GroupSafety

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma listedSafe_le_rank_gap (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (ε : Fin 2) :
    (listedSafeStatistic M hE κ d s i Y ε : ℝ) ≤
      (κ : ℝ) * listedRankStatistic M hE κ d s i ε + listedTransferGap M hE κ d s i Y ε := by
  unfold listedTransferGap
  have hh := le_max_left ((listedSafeStatistic M hE κ d s i Y ε : ℝ) -
    (κ : ℝ) * listedRankStatistic M hE κ d s i ε) 0
  linarith

theorem listedRankStatistic_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d s i).card) / densityThreshold ≤
      tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        univ (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2^100) (withMasks d D C T) s i (boolParity p) : ℝ))) := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  have hsafe := listedSafeStatistic_lower M hE (2^100) (by positivity) d s i Y hY hI
    (fun _ => thinningRate) (fun _ => ht0) (fun _ => ht1)
  have herr := listedTransferGap_parity_expectation_le M hE d s i Y hY hn
  have hkcast : ((2^100 : ℕ) : ℝ) = densityThreshold := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold]
  rw [hkcast] at hsafe
  have hdet (D C T : Finset (Fin n)) :
      fairParityExpectation (fun p => (listedSafeStatistic M hE (2^100)
        (withMasks d D C T) s i Y (boolParity p) : ℝ)) ≤
      densityThreshold * fairParityExpectation (fun p => (listedRankStatistic M hE (2^100)
        (withMasks d D C T) s i (boolParity p) : ℝ)) +
      fairParityExpectation (fun p => listedTransferGap M hE (2^100)
        (withMasks d D C T) s i Y (boolParity p)) := by
    have h0 := listedSafe_le_rank_gap M hE (2^100) (withMasks d D C T) s i Y (boolParity false)
    have h1 := listedSafe_le_rank_gap M hE (2^100) (withMasks d D C T) s i Y (boolParity true)
    rw [hkcast] at h0 h1
    dsimp only [fairParityExpectation]
    calc
      _ ≤ _ := div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num : (0:ℝ) ≤ 2)
      _ = _ := by ring
  have hmean := tripleMaskExpectation_mono (fun _ : Fin n => (1:ℝ)/4)
    (fun _ => thinningRate) (fun _ => thinningRate) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1) univ
    (fun D _ C _ T _ => hdet D C T)
  rw [tripleMaskExpectation_add, tripleMaskExpectation_mul] at hmean
  have hc := mul_le_mul_of_nonneg_right residual_error_constant
    (Nat.cast_nonneg (trueGroup M d s i).card)
  apply (div_le_iff₀ constants_positive.2.1).2
  rw [div_eq_mul_inv] at hsafe
  nlinarith

end MatroidProphet.MainAlgorithm

end OAI
