import OAI.Probability.MatroidProphet.Algorithm.Cost
import OAI.Probability.MatroidProphet.Algorithm.Mean
import OAI.Probability.MatroidProphet.GroupTransfer

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma trueGroup_eq_candidate_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) :
    trueGroup M d w i = (candidateLabels M w d.H).filter (fun e => w e = some i) := by
  unfold trueGroup candidateLabels candidateSet
  ext e
  simp only [mem_filter, mem_univ, true_and]
  rfl

noncomputable def higherTrueGroups (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) : Finset (Fin n) :=
  (candidateLabels M w d.H).filter (fun e => ∃ k, w e = some k ∧ i < k)

lemma trueZ_eq_listedRankStatistic (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    trueZ M hE d w i = listedRankStatistic M hE (2^100) d w i (boolParity d.odd) := by
  unfold trueZ listedRankStatistic
  split_ifs with hi
  · unfold listedZ
    rw [groupMask_at_key M d w univ _ i (groups_get?_idxOf M d w i hi), univ_inter]
  · rfl

lemma mainMean_trueZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) =
      tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        univ (fun D C T => fairParityExpectation (fun p =>
          (listedRankStatistic M hE (2^100) (withMasks d D C T) w i (boolParity p) : ℝ))) := by
  unfold mainMean
  apply tripleMaskExpectation_congr
  intro D hD C hC T hT
  congr 1
  funext p
  dsimp only
  rw [trueZ_eq_listedRankStatistic]
  rfl

theorem mainMean_trueZ_lower (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d w i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ)) :
    (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) / densityThreshold ≤
      mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) := by
  rw [mainMean_trueZ]
  exact listedRankStatistic_lower M hE d w i Y hY hI hn

lemma true_expected_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    densityThreshold * t * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (trueZ M hE {d with T := T} w i : ℝ)) ≤
    densityThreshold * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (trueLambda M hE {d with T := T} w i : ℝ)) +
      t * (densityThreshold * (d.C ∩ trueGroup M d w i).card +
        densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card) := by
  by_cases hi : i ∈ groups M d w
  · have hh : (groups M d w).idxOf i < (groups M d w).length := List.idxOf_lt_length_of_mem hi
    have hl := listed_expected_nominal_to_final M hE d w _ hh t ht0 ht1
    have hc := listed_cost_le_true_counts M d w (groups_get?_idxOf M d w i hi) (2^100)
    rw [← trueGroup_eq_candidate_filter M d w i] at hc
    have hc' : (((2^100) * (groupMask M d w d.C ((groups M d w).idxOf i)).ncard +
        ∑ j ∈ range ((groups M d w).length-((groups M d w).idxOf i+1)),
          ((2^100) * (groupMask M d w d.C ((groups M d w).idxOf i+1+j)).ncard +
            (groupMask M d w d.D ((groups M d w).idxOf i+1+j)).ncard) : ℕ) : ℝ) ≤
        densityThreshold * (d.C ∩ trueGroup M d w i).card +
          densityThreshold * (d.C ∩ higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card := by
      calc
        _ ≤ (((2^100) * (d.C ∩ trueGroup M d w i).card +
          (2^100) * (d.C ∩ higherTrueGroups M d w i).card +
          (higherTrueGroups M d w i).card : ℕ) : ℝ) := by exact_mod_cast hc
        _ = _ := by norm_num [densityThreshold]
    have hz (T : Finset (Fin n)) : trueZ M hE {d with T := T} w i =
        listedZ M hE {d with T := T} w ((groups M d w).idxOf i) := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_left hi]
      rfl
    have hLam (T : Finset (Fin n)) : trueLambda M hE {d with T := T} w i =
        listedLambda M hE {d with T := T} w ((groups M d w).idxOf i) := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_left hi]
      rfl
    simp only [hz, hLam]
    exact hl.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc' ht0))
  · have hz (T : Finset (Fin n)) : trueZ M hE {d with T := T} w i = 0 := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_right hi]
    have hLam (T : Finset (Fin n)) : trueLambda M hE {d with T := T} w i = 0 := by
      change (if i ∈ groups M d w then _ else 0) = _
      rw [ite_eq_right hi]
    simp only [hz, hLam, Nat.cast_zero, bitsExpectation_const, mul_zero, zero_add]
    apply mul_nonneg ht0
    exact add_nonneg (add_nonneg
      (mul_nonneg constants_positive.2.1.le (Nat.cast_nonneg _))
      (mul_nonneg constants_positive.2.1.le (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

lemma trueGroup_eq_of_H_eq (M : Matroid (Fin n)) (d d' : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) (hH : d'.H = d.H) :
    trueGroup M d' w i = trueGroup M d w i := by
  rw [trueGroup_eq_candidate_filter, trueGroup_eq_candidate_filter, hH]

lemma higherTrueGroups_eq_of_H_eq (M : Matroid (Fin n)) (d d' : MainMasks n)
    (w : Fin n → Option ℤ) (i : ℤ) (hH : d'.H = d.H) :
    higherTrueGroups M d' w i = higherTrueGroups M d w i := by
  simp only [higherTrueGroups, hH]

lemma mainMean_resample_test (d : MainMasks n) (f : MainMasks n → ℝ) :
    mainMean d (fun d' => bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun T => f {d' with T := T})) = mainMean d f := by
  unfold mainMean tripleMaskExpectation
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  change bitsExpectation (fun _ : Fin n => thinningRate) univ (fun _ =>
      fairParityExpectation (fun p => bitsExpectation (fun _ : Fin n => thinningRate) univ
        (fun T => f {withMasks d D C T with odd := p}))) = _
  rw [bitsExpectation_const, ← bitsExpectation_fairParity]

theorem mainMean_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) :
    densityThreshold * thinningRate * mainMean d (fun d' => (trueZ M hE d' w i : ℝ)) ≤
      densityThreshold * mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) +
        thinningRate * (densityThreshold * thinningRate * (trueGroup M d w i).card +
          densityThreshold * thinningRate * (higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card) := by
  have hmean : mainMean d (fun d' => densityThreshold * thinningRate *
      bitsExpectation (fun _ : Fin n => thinningRate) univ (fun T =>
        (trueZ M hE {d' with T := T} w i : ℝ))) ≤
      mainMean d (fun d' => densityThreshold *
        bitsExpectation (fun _ : Fin n => thinningRate) univ (fun T =>
          (trueLambda M hE {d' with T := T} w i : ℝ)) +
        thinningRate * (densityThreshold * (d'.C ∩ trueGroup M d w i).card +
          densityThreshold * (d'.C ∩ higherTrueGroups M d w i).card +
            (higherTrueGroups M d w i).card)) := by
    apply mainMean_mono
    intro d' hH
    have hp := true_expected_nominal_to_final M hE d' w i thinningRate
      constants_positive.2.2.1.le (by norm_num [thinningRate])
    rwa [trueGroup_eq_of_H_eq M d d' w i hH,
      higherTrueGroups_eq_of_H_eq M d d' w i hH] at hp
  simp only [mainMean_add, mainMean_mul, mainMean_const, mainMean_guard_count] at hmean
  rw [mainMean_resample_test d (fun d' => (trueZ M hE d' w i : ℝ)),
    mainMean_resample_test d (fun d' => (trueLambda M hE d' w i : ℝ))] at hmean
  simpa only [mul_assoc] using hmean

theorem true_group_payoff (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d w i : Set (Fin n))) (hI : M.Indep Y)
    (hn : densityThreshold ≤ ((trueGroup M d w i).card : ℝ)) :
    thinningRate / densityThreshold *
        (retainedFraction * Y.ncard -
          (((2:ℝ)^23)⁻¹ + thinningRate * densityThreshold) * (trueGroup M d w i).card -
          (1 + thinningRate * densityThreshold) * (higherTrueGroups M d w i).card) ≤
      mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) := by
  have hZ := mainMean_trueZ_lower M hE d w i Y hY hI hn
  have hcost := mainMean_nominal_to_final M hE d w i
  have hk : 0 < densityThreshold := constants_positive.2.1
  have ht : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have hmul := mul_le_mul_of_nonneg_left hZ (mul_nonneg hk.le ht)
  have hcancel : densityThreshold * thinningRate *
      ((retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) / densityThreshold) =
      thinningRate * (retainedFraction * Y.ncard - ((2:ℝ)^23)⁻¹ * (trueGroup M d w i).card) := by
    field_simp
  rw [hcancel] at hmul
  have hboth := hmul.trans hcost
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk).mpr
  nlinarith [hboth]

end MatroidProphet.MainAlgorithm

end OAI
