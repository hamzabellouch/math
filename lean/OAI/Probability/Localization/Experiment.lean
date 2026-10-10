import OAI.Probability.Localization.Model

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma continuous_chart (n : ℕ) : Continuous (@chart n) := by
  apply continuous_pi
  intro a
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simp only [chart, Fin.lastCases_last]
    fun_prop
  · simp only [chart, Fin.lastCases_castSucc]
    fun_prop

lemma measurable_chart (n : ℕ) : Measurable (@chart n) :=
  (continuous_chart n).measurable

lemma continuous_exactLabel (n : ℕ) :
    Continuous (fun Xz : GaussianBlock n × Coordinate n => exactLabel Xz.1 Xz.2) := by
  apply continuous_pi
  intro row
  unfold exactLabel
  apply continuous_finsetSum
  intro coordinate _
  exact ((continuous_apply coordinate).comp ((continuous_apply row).comp continuous_fst)).mul
    ((continuous_apply coordinate).comp ((continuous_chart n).comp continuous_snd))

lemma measurable_initialCube (n : ℕ) : MeasurableSet (initialCube n) := by
  apply MeasurableSet.univ_pi
  intro _
  exact measurableSet_Ico

lemma volume_initialCube (n : ℕ) :
    volume (initialCube n) = ENNReal.ofReal ((1 / Real.sqrt n) ^ n) := by
  unfold initialCube
  rw [Real.volume_pi_Ico]
  have hw : 1 / (2 * Real.sqrt n) - -1 / (2 * Real.sqrt n) = 1 / Real.sqrt n := by
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

lemma volume_initialCube_pos {n : ℕ} (hn : 0 < n) :
    0 < volume (initialCube n) := by
  rw [volume_initialCube]
  exact ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)

lemma volume_initialCube_ne_top (n : ℕ) : volume (initialCube n) ≠ ∞ := by
  rw [volume_initialCube]
  exact ENNReal.ofReal_ne_top

lemma cubePrior_isProbabilityMeasure {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (cubePrior n) := by
  exact cond_isProbabilityMeasure_of_finite
    (ne_of_gt (volume_initialCube_pos hn)) (volume_initialCube_ne_top n)

instance gaussianBlockLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianBlockLaw n) := by
  unfold gaussianBlockLaw
  infer_instance

lemma BlockRule.prob_le_one {n N : ℕ} (rule : BlockRule n N)
    (data : GaussianBlock n × Label n) (w : Fin N) : rule.prob data w ≤ 1 := by
  rw [← rule.sum_one data]
  exact Finset.single_le_sum (fun i _ => rule.nonneg data i) (Finset.mem_univ w)

lemma measurable_actualRule {n N : ℕ} (rule : BlockRule n N) (w : Fin N) :
    Measurable (fun Xz : GaussianBlock n × Coordinate n =>
      rule.prob (Xz.1, exactLabel Xz.1 Xz.2) w) :=
  (rule.measurable_prob w).comp
    (measurable_fst.prodMk (continuous_exactLabel n).measurable)

lemma integrable_actualRule {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) :
    Integrable (fun X => rule.prob (X, exactLabel X z) w) (gaussianBlockLaw n) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_actualRule rule w).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rule.nonneg _ w)]
      exact rule.prob_le_one _ w)

lemma measurable_blockProbability {n N : ℕ} (rule : BlockRule n N) (w : Fin N) :
    Measurable (fun z => blockProbability rule z w) := by
  exact (measurable_actualRule rule w).stronglyMeasurable.integral_prod_left'.measurable

lemma blockProbability_nonneg {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) : 0 ≤ blockProbability rule z w := by
  exact integral_nonneg (fun X => rule.nonneg _ w)

lemma blockProbability_sum {n N : ℕ} (rule : BlockRule n N) (z : Coordinate n) :
    ∑ w, blockProbability rule z w = 1 := by
  unfold blockProbability
  rw [← integral_finsetSum _ (fun w _ => integrable_actualRule rule z w)]
  simp [rule.sum_one]

lemma blockProbability_le_one {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) : blockProbability rule z w ≤ 1 := by
  rw [← blockProbability_sum rule z]
  exact Finset.single_le_sum (fun j _ => blockProbability_nonneg rule z j)
    (Finset.mem_univ w)

lemma measurable_historyLikelihood {n N t : ℕ} (rules : Rules n N t) (w : History N t) :
    Measurable (fun z => historyLikelihood rules z w) := by
  exact Finset.measurable_prod _ (fun i _ => measurable_blockProbability (rules i (past w i)) (w i))

lemma historyLikelihood_nonneg {n N t : ℕ} (rules : Rules n N t)
    (z : Coordinate n) (w : History N t) : 0 ≤ historyLikelihood rules z w := by
  exact Finset.prod_nonneg (fun i _ => blockProbability_nonneg _ _ _)

lemma historyLikelihood_le_one {n N t : ℕ} (rules : Rules n N t)
    (z : Coordinate n) (w : History N t) : historyLikelihood rules z w ≤ 1 := by
  exact Finset.prod_le_one₀ (fun _ _ => blockProbability_nonneg _ _ _)
    (fun _ _ => blockProbability_le_one _ _ _)

end RepeatedLocalization

end OAI
