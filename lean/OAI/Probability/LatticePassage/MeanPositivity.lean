import OAI.Probability.LatticePassage.MeanTimeConstant
import OAI.Probability.LatticePassage.LatticeMetric

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

lemma passageTime_mean_lower_of_tail (x y : Vertex) (t b : ℝ) (ht : 0 ≤ t)
    (hb : environmentLaw.real {ω : Environment | passageTime ω x y ≤ t} ≤ b) :
    t*(1-b) ≤ ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  classical
  let F := {ω : Environment | passageTime ω x y ≤ t}
  have hF : MeasurableSet F := measurableSet_le (measurable_passageTime x y) measurable_const
  have hi := integral_mono_ae ((integrable_const t).indicator hF.compl)
    (integrable_passageTime x y) (by
      filter_upwards [passageTime_properties] with ω hω
      by_cases hf : ω ∈ Fᶜ
      · rw [Set.indicator_of_mem hf]
        exact (lt_of_not_ge (show ¬ passageTime ω x y ≤ t from hf)).le
      · rw [Set.indicator_of_notMem hf]
        exact hω.1 x y)
  rw [integral_indicator_const t hF.compl] at hi
  have hu : environmentLaw.real Set.univ = 1 := by simp [measureReal_def]
  simp only [smul_eq_mul, measureReal_compl hF, hu] at hi
  have he : t*(1-b) ≤ (1-environmentLaw.real F)*t := by
    nlinarith
  exact he.trans hi

private lemma small_tail_at_most_half (d : ℕ) (hd : 8 ≤ d) :
    (8/3 : ℝ)*exp (-(log 2/2)*d) ≤ 1/2 := by
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have he : exp (-(log 2/2)*d) ≤ exp (-((4 : ℕ)*log 2)) := by
    rw [exp_le_exp]
    norm_num
    nlinarith
  have hv : exp (-((4 : ℕ)*log (2 : ℝ))) = 1/16 := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hv] at he
  linarith

theorem passageTime_mean_linear_lower (x y : Vertex) (hd : 8 ≤ latticeDistance x y) :
    (log 2/20)*latticeDistance x y ≤
      ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  have hb := (passageTime_small_linear_tail x y (by omega)).trans
    (small_tail_at_most_half (latticeDistance x y) hd)
  have hm := passageTime_mean_lower_of_tail x y ((log 2/10)*latticeDistance x y)
    (1/2) (by positivity) hb
  nlinarith

lemma latticeDistance_scaleVertex (n : ℕ) (x : Vertex) :
    latticeDistance 0 (scaleVertex n x) = n*latticeDistance 0 x := by
  simp [latticeDistance, scaleVertex, Int.natAbs_mul, Nat.mul_add]

theorem directionalMeanConstant_linear_lower (x : Vertex) :
    (log 2/20)*latticeDistance 0 x ≤ directionalMeanConstant x := by
  by_cases hx : latticeDistance 0 x = 0
  · simpa only [hx, Nat.cast_zero, mul_zero] using directionalMeanConstant_nonneg x
  have hd : 1 ≤ latticeDistance 0 x := by omega
  apply ge_of_tendsto (meanPassageSequence_tendsto x)
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn
  have hnd : 8 ≤ latticeDistance 0 (scaleVertex n x) := by
    rw [latticeDistance_scaleVertex]
    nlinarith
  have hm := passageTime_mean_linear_lower 0 (scaleVertex n x) hnd
  rw [latticeDistance_scaleVertex, Nat.cast_mul] at hm
  change (log 2/20)*((n : ℝ)*latticeDistance 0 x) ≤ meanPassageSequence x n at hm
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))).mpr
  nlinarith

theorem directionalMeanConstant_pos {x : Vertex} (hx : x ≠ 0) :
    0 < directionalMeanConstant x := by
  have hd : 0 < latticeDistance 0 x := by
    by_contra h
    have he : x.1 = 0 ∧ x.2 = 0 := by
      have hn : x.1.natAbs = 0 ∧ x.2.natAbs = 0 := by
        simp [latticeDistance] at h
        omega
      simpa only [Int.natAbs_eq_zero] using hn
    exact hx (Prod.ext he.1 he.2)
  exact lt_of_lt_of_le (by positivity) (directionalMeanConstant_linear_lower x)

end CompanionFPP

end OAI
