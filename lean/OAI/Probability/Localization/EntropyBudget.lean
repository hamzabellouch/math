import OAI.Probability.Localization.TruncatedBounds
import OAI.Probability.Localization.EntropyChain

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def entropySlope (n : ℕ) : ℝ := (n:ℝ)*Real.log 2/2

noncomputable def historyKL {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : ℝ≥0∞ :=
  InformationTheory.klDiv (ProbabilityTheory.cond P (state P Q h).event) (uniformCell (state P Q h).cell)

noncomputable def historyCost {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) : ℝ :=
  (historyKL P Q h).toReal + entropySlope n * ((state P Q h).cell.1-Q.1 : ℕ)

lemma entropySlope_pos {n : ℕ} (hn : 0 < n) : 0 < entropySlope n := by
  unfold entropySlope
  exact div_pos (mul_pos (Nat.cast_pos.mpr hn) (Real.log_pos (by norm_num))) (by norm_num)

lemma historyCost_nonneg {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    0 ≤ historyCost P Q h := by
  unfold historyCost entropySlope
  exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) (by norm_num)) (Nat.cast_nonneg _))

lemma historyKL_ne_top_budget {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    historyKL P Q h ≠ ∞ ∧
    (P (state P Q h).event).toReal * historyCost P Q h ≤
      (∫ z in (state P Q h).event,llr P (uniformCell Q) z ∂P) +
        (P (state P Q h).event).toReal * rewardLog P Q (complementReward P) h := by
  let := uniformCell_probability hn Q
  have hd := positive_event_descendant P Q h hp
  have hk := klDiv_cond_cond P (uniformCell Q) hac hK (state_event_measurable P Q h)
    (measurableSet_cellSet _) (state_event_subset_cell P Q h) hp (uniformCell_descendant_pos hn hd)
  rw [uniformCell_cond hd,uniformCell_log_mass hn hd] at hk
  refine ⟨hk.1,?_⟩
  have hroot : P (cellSet Q) = 1 := (mem_ae_iff_prob_eq_one (measurableSet_cellSet Q)).mp (ae_mem_cell_of_ac hac)
  have hs := mul_le_mul_of_nonneg_left (path_label_surprisal P Q hroot h hp) (ENNReal.toReal_nonneg (a := P (state P Q h).event))
  have he := hk.2
  change (P (state P Q h).event).toReal * ((historyKL P Q h).toReal + entropySlope n * _) ≤ _
  change (P (state P Q h).event).toReal * (historyKL P Q h).toReal = _ at he
  unfold entropySlope
  nlinarith

lemma truncated_cost_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => historyCost P Q (run P Q N z)) P ∧
    (∫ z,historyCost P Q (run P Q N z) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + ∫ z,complementTotal P Q N z ∂P := by
  let := uniformCell_probability hn Q
  have hroot := ae_mem_cell_of_ac hac
  have hi := (InformationTheory.klDiv_ne_top_iff.mp hK).2
  have hJ := (truncated_reward_bounds hn P Q hroot N).1
  have hb (h : Log n) : (P {z | run P Q N z = h}).toReal * historyCost P Q h ≤
      ∫ z in {z | run P Q N z = h},llr P (uniformCell Q) z + complementTotal P Q N z ∂P := by
    by_cases hp : P {z | run P Q N z = h} = 0
    · rw [hp,ENNReal.toReal_zero,zero_mul,Measure.restrict_eq_zero.mpr hp,integral_zero_measure]
    obtain ⟨z,hz,hzh⟩ := exists_run_fiber_root P Q hroot N h hp
    have he : {w | run P Q N w = h} =ᵐ[P] (state P Q h).event := by
      simpa only [hzh] using run_fiber_ae_event hn P Q hroot N hz
    have hp' : P (state P Q h).event ≠ 0 := by rwa [← measure_congr he]
    have hb := (historyKL_ne_top_budget hn P Q hac hK h hp').2
    rw [integral_add hi.integrableOn hJ.integrableOn]
    change _ ≤ (∫ z in {z | run P Q N z = h},llr P (uniformCell Q) z ∂P) +
      ∫ z in {z | run P Q N z = h},(fun h => rewardLog P Q (complementReward P) h) (run P Q N z) ∂P
    rw [integral_comp_fiber P (run P Q N) (rewardLog P Q (complementReward P)) h
      ((measurable_run hn P Q N) (measurableSet_singleton h)),Measure.restrict_congr_set he,measure_congr he]
    exact hb
  have hb' := countable_cost_bound P (run P Q N) (measurable_run hn P Q N)
    (historyCost P Q) (historyCost_nonneg P Q) (hi.add hJ) hb
  simp only [Pi.add_apply] at hb'
  rw [integral_add hi hJ,← InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)] at hb'
  exact hb'

lemma truncated_depth_integrable {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => (truncatedDepth P Q N z : ℝ)) P := by
  have hc := (truncated_cost_bound hn P Q hac hK N).1
  have hm : Measurable (fun z => (truncatedDepth P Q N z : ℝ)) :=
    (measurable_of_countable (fun h : Log n => (((state P Q h).cell.1-Q.1:ℕ):ℝ))).comp (measurable_run hn P Q N)
  apply Integrable.mono' (hc.div_const (entropySlope n)) hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),le_div_iff₀ (entropySlope_pos hn)]
  change _ ≤ (historyKL P Q (run P Q N z)).toReal + entropySlope n * (truncatedDepth P Q N z:ℝ)
  nlinarith [ENNReal.toReal_nonneg (a := historyKL P Q (run P Q N z))]

lemma truncated_KL_integrable {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    Integrable (fun z => (historyKL P Q (run P Q N z)).toReal) P := by
  have hc := (truncated_cost_bound hn P Q hac hK N).1
  have hd := truncated_depth_integrable hn P Q hac hK N
  have he : (fun z => (historyKL P Q (run P Q N z)).toReal) =
      (fun z => historyCost P Q (run P Q N z)) - (fun z => entropySlope n*(truncatedDepth P Q N z:ℝ)) := by
    funext z
    simp [historyCost,truncatedDepth]
  rw [he]
  exact hc.sub (hd.const_mul _)

lemma truncated_attempts_integral {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(truncatedAttempts P Q N z:ℝ) ∂P) ≤ 2*(1+∫ z,(truncatedDepth P Q N z:ℝ) ∂P) := by
  have hroot := ae_mem_cell_of_ac hac
  have hC := (truncated_reward_bounds hn P Q hroot N).2
  have hD := truncated_depth_integrable hn P Q hac hK N
  have hp : ∀ᵐ z ∂P,(truncatedAttempts P Q N z:ℝ) ≤
      (truncatedDepth P Q N z:ℝ) + continuingTotal P Q N z + 1 := by
    filter_upwards [hroot] with z hz
    have hb := truncated_attempts_path hn P Q N hz
    have hs : (if (state P Q (run P Q N z)).stopped then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
    linarith
  have hi := integral_mono_ae (integrable_truncatedAttempts hn P Q N)
    ((hD.add hC.1).add (integrable_const 1)) hp
  have had := integral_add (hD.add hC.1) (integrable_const (1:ℝ))
  simp only [Pi.add_apply] at hi had
  rw [had,integral_add hD hC.1] at hi
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hi
  linarith [hC.2.2]

lemma slope_absorption {n : ℕ} (hn : 32 ≤ n) : 2/Real.exp 1 ≤ entropySlope n/2 := by
  have hn' : (32:ℝ) ≤ n := by exact_mod_cast hn
  have hl : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : (2:ℝ)/Real.exp 1 ≤ 2 := (div_le_self (by norm_num) (Real.one_le_exp (by norm_num)))
  unfold entropySlope
  nlinarith

lemma truncated_final_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(historyKL P Q (run P Q N z)).toReal + entropySlope n/2*(truncatedDepth P Q N z:ℝ) ∂P) ≤
      (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by
  have hn0 : 0 < n := by omega
  have hcost := (truncated_cost_bound hn0 P Q hac hK N).2
  have hJ := (truncated_reward_bounds hn0 P Q (ae_mem_cell_of_ac hac) N).2.2.1
  have hA := truncated_attempts_integral hn0 P Q hac hK N
  have hD := truncated_depth_integrable hn0 P Q hac hK N
  have hKI := truncated_KL_integrable hn0 P Q hac hK N
  change (∫ z,(historyKL P Q (run P Q N z)).toReal + entropySlope n*(truncatedDepth P Q N z:ℝ) ∂P) ≤ _ at hcost
  rw [integral_add hKI (hD.const_mul (entropySlope n)),integral_const_mul] at hcost
  rw [integral_add hKI (hD.const_mul (entropySlope n / 2)),integral_const_mul]
  have hD0 : 0 ≤ ∫ z,(truncatedDepth P Q N z:ℝ) ∂P := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have habs := mul_le_mul_of_nonneg_right (slope_absorption hn) hD0
  have hJA := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ (1:ℝ)/Real.exp 1)
  simp only [div_eq_mul_inv,one_mul] at hJ hJA habs ⊢
  nlinarith only [hcost,hJ,habs,hJA]

end FiniteEntropy

end RepeatedLocalization

end OAI
