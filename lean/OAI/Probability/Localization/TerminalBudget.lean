import OAI.Probability.Localization.Termination

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def terminalKL {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) : ℝ≥0∞ :=
  InformationTheory.klDiv (terminalLaw P Q (terminalLog P Q z))
    (uniformCell (terminalCell P Q (terminalLog P Q z)))

lemma measurable_terminalKL {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (terminalKL P Q) :=
  (measurable_of_countable (fun h : Log n => InformationTheory.klDiv (terminalLaw P Q h)
    (uniformCell (terminalCell P Q h)))).comp (measurable_terminalLog hn P Q)

lemma measurable_depth_real {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (fun z => (depth P Q z:ℝ)) :=
  (measurable_of_countable (fun h : Log n => (((terminalCell P Q h).1-Q.1:ℕ):ℝ))).comp
    (measurable_terminalLog hn P Q)

lemma terminal_historyKL {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    terminalKL P Q z = historyKL P Q (terminalLog P Q z) := by
  unfold terminalKL historyKL terminalLaw terminalCell
  rw [cond_congr_ae P (terminal_fiber_ae_event hn P Q hroot hz ht)]

lemma terminal_cost_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ)) P ∧
      (∫ z,(terminalKL P Q z).toReal + entropySlope n/2*(depth P Q z:ℝ) ∂P) ≤
        (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by
  have hn0 : 0 < n := by omega
  have hs : 0 ≤ entropySlope n/2 := le_of_lt (div_pos (entropySlope_pos hn0) (by norm_num))
  apply frozen_nonnegative_bound P
    (fun N z => (historyKL P Q (run P Q N z)).toReal + entropySlope n/2*(truncatedDepth P Q N z:ℝ))
    _ _ (budget_nonneg P Q)
  · intro N
    exact (truncated_KL_integrable hn0 P Q hac hK N).add
      ((truncated_depth_integrable hn0 P Q hac hK N).const_mul _)
  · intro N z
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hs (Nat.cast_nonneg _))
  · exact ((measurable_terminalKL hn0 P Q).ennreal_toReal.add
      ((measurable_depth_real hn0 P Q).const_mul _)).aestronglyMeasurable
  · intro z
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hs (Nat.cast_nonneg _))
  · have hroot := ae_mem_cell_of_ac hac
    filter_upwards [hroot,almost_sure_termination hn P Q hac hK] with z hz ht
    refine ⟨attempts P Q z,fun M hM => ?_⟩
    have he := run_eventually_terminal P Q ht M hM
    simp only [truncatedDepth,he,← terminal_historyKL hn0 P Q hroot hz ht,depth,terminalCell]
  · exact truncated_final_budget hn P Q hac hK

lemma terminal_depth_integrable {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (depth P Q z:ℝ)) P := by
  have hn0 : 0 < n := by omega
  have hc := (terminal_cost_budget hn P Q hac hK).1
  apply Integrable.mono' (hc.div_const (entropySlope n/2)) (measurable_depth_real hn0 P Q).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),le_div_iff₀ (div_pos (entropySlope_pos hn0) (by norm_num))]
  nlinarith [ENNReal.toReal_nonneg (a := terminalKL P Q z)]

lemma terminal_KL_integrable {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (terminalKL P Q z).toReal) P := by
  have hc := (terminal_cost_budget hn P Q hac hK).1
  have hd := terminal_depth_integrable hn P Q hac hK
  simpa only [add_sub_cancel_right] using
    hc.sub' (hd.const_mul (entropySlope n/2))

lemma terminal_attempts_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    Integrable (fun z => (attempts P Q z:ℝ)) P ∧
      (∫ z,(attempts P Q z:ℝ) ∂P) ≤ 2*(1+∫ z,(depth P Q z:ℝ) ∂P) := by
  have hn0 : 0 < n := by omega
  have hroot := ae_mem_cell_of_ac hac
  have hterm := almost_sure_termination hn P Q hac hK
  have hd := terminal_depth_integrable hn P Q hac hK
  apply frozen_nonnegative_bound P (fun N z => (truncatedAttempts P Q N z:ℝ)) _ _
  · positivity
  · exact integrable_truncatedAttempts hn0 P Q
  · intro N z
    exact Nat.cast_nonneg _
  · exact ((measurable_of_countable (fun a : ℕ => (a:ℝ))).comp (measurable_attempts hn0 P Q)).aestronglyMeasurable
  · intro z
    exact Nat.cast_nonneg _
  · filter_upwards [hterm] with z ht
    refine ⟨attempts P Q z,fun M hM => ?_⟩
    simp only [truncatedAttempts,run_eventually_terminal P Q ht M hM,terminalLog_length P Q ht]
  · intro N
    have he : ∀ᵐ z ∂P,(truncatedDepth P Q N z:ℝ) ≤ (depth P Q z:ℝ) := by
      filter_upwards [hroot,hterm] with z hz ht
      have hm := truncatedDepth_mono hn0 P Q hz (Nat.le_max_left N (attempts P Q z))
      have hf := run_eventually_terminal P Q ht (max N (attempts P Q z)) (Nat.le_max_right _ _)
      simp only [truncatedDepth,hf] at hm
      exact_mod_cast hm
    have hi := integral_mono_ae (truncated_depth_integrable hn0 P Q hac hK N) hd he
    exact (truncated_attempts_integral hn0 P Q hac hK N).trans (by linarith)

lemma terminal_ennreal_budget {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    (∫⁻ z,terminalKL P Q z ∂P) + ENNReal.ofReal ((Real.log 2/4)*n*(∫ z,(depth P Q z:ℝ) ∂P)) ≤
      InformationTheory.klDiv P (uniformCell Q) + ENNReal.ofReal (2/Real.exp 1) := by
  have hd := terminal_depth_integrable hn P Q hac hK
  have hk := terminal_KL_integrable hn P Q hac hK
  have hc := (terminal_cost_budget hn P Q hac hK).2
  rw [integral_add hk (hd.const_mul _),integral_const_mul] at hc
  have hfin : ∀ᵐ z ∂P,terminalKL P Q z ≠ ∞ := by
    filter_upwards [ae_fiber_positive P (terminalLog P Q)] with z hz
    exact (terminal_regular hn P Q hac hK (terminalLog P Q z) hz).2.2
  have he : (∫⁻ z,terminalKL P Q z ∂P) = ENNReal.ofReal (∫ z,(terminalKL P Q z).toReal ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))]
    exact lintegral_congr_ae (hfin.mono (fun z hz => (ENNReal.ofReal_toReal hz).symm))
  have hs : (Real.log 2/4)*(n:ℝ) = entropySlope n/2 := by unfold entropySlope; ring
  rw [he,hs,← ENNReal.ofReal_add (integral_nonneg (fun _ => ENNReal.toReal_nonneg))]
  calc
    _ ≤ ENNReal.ofReal ((InformationTheory.klDiv P (uniformCell Q)).toReal+2/Real.exp 1) := ENNReal.ofReal_le_ofReal hc
    _ = _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hK]
      positivity
  · exact mul_nonneg (le_of_lt (div_pos (entropySlope_pos (by omega)) (by norm_num)))
      (integral_nonneg (fun _ => Nat.cast_nonneg _))

end FiniteEntropy

end RepeatedLocalization

end OAI
