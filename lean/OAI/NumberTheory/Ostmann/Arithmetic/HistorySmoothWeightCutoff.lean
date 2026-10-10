import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import OAI.NumberTheory.Ostmann.Section07SmoothPartitionDerivative

namespace OAI

namespace Ostmann.Arithmetic
open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable def giantCell (G p : ℝ) : ℝ :=
  if 0 < p then smoothPartition (Real.log p - G) else 0

@[simp] theorem giantCell_of_pos (G : ℝ) {p : ℝ} (hp : 0 < p) :
    giantCell G p = smoothPartition (Real.log p - G) := by
  simp only [giantCell, ite_eq_left hp]

@[simp] theorem giantCell_of_nonpos (G : ℝ) {p : ℝ} (hp : p ≤ 0) : giantCell G p = 0 := by
  simp only [giantCell, ite_eq_right (not_lt_of_ge hp)]

theorem giantCell_bounds (G p : ℝ) : 0 ≤ giantCell G p ∧ giantCell G p ≤ 1 := by
  by_cases hp : 0 < p
  · rw [giantCell_of_pos G hp]
    exact ⟨smoothPartition_nonneg _, smoothPartition_le_one _⟩
  · rw [giantCell_of_nonpos G (le_of_not_gt hp)]
    exact ⟨le_rfl, zero_le_one⟩

theorem giantCell_zero_of_le_lower (G : ℝ) {p : ℝ} (hp : p ≤ Real.exp (G - 1)) :
    giantCell G p = 0 := by
  by_cases hpos : 0 < p
  · rw [giantCell_of_pos G hpos]
    apply smoothPartition_zero_of_le_neg_one
    have hlog := (Real.log_le_iff_le_exp hpos).mpr hp
    linarith
  · exact giantCell_of_nonpos G (le_of_not_gt hpos)

theorem giantCell_zero_of_upper_le (G : ℝ) {p : ℝ} (hp : Real.exp (G + 1) ≤ p) :
    giantCell G p = 0 := by
  have hpos : 0 < p := (Real.exp_pos _).trans_le hp
  rw [giantCell_of_pos G hpos]
  apply smoothPartition_zero_of_one_le
  have hlog := Real.log_le_log (Real.exp_pos (G + 1)) hp
  rw [Real.log_exp] at hlog
  linarith

theorem giantCell_eventually_zero (G : ℝ) {p : ℝ} (hp : p ≤ 0) :
    giantCell G =ᶠ[𝓝 p] 0 := by
  have hlt : p < Real.exp (G - 1) := hp.trans_lt (Real.exp_pos _)
  filter_upwards [eventually_lt_nhds hlt] with y hy
  exact giantCell_zero_of_le_lower G hy.le

@[fun_prop] theorem giantCell_contDiff (G : ℝ) : ContDiff ℝ ∞ (giantCell G) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : 0 < p
  · have hc : ContDiffAt ℝ ∞ (fun y : ℝ => smoothPartition (Real.log y - G)) p :=
      smoothPartition_contDiff.contDiffAt.comp p
        ((contDiffAt_id.log hp.ne').sub contDiffAt_const)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hp] with y hy
    exact giantCell_of_pos G hy
  · exact contDiffAt_const.congr_of_eventuallyEq (giantCell_eventually_zero G (le_of_not_gt hp))

theorem giantCell_log_deriv (G : ℝ) {p : ℝ} (hp : 0 < p) :
    p * deriv (giantCell G) p = deriv smoothPartition (Real.log p - G) := by
  have hφ := ((smoothPartition_contDiff.differentiable (by simp)) (Real.log p - G)).hasDerivAt
  have h := hφ.comp p ((Real.hasDerivAt_log hp.ne').sub_const G)
  have heq : giantCell G =ᶠ[𝓝 p] (fun y : ℝ => smoothPartition (Real.log y - G)) := by
    filter_upwards [eventually_gt_nhds hp] with y hy
    exact giantCell_of_pos G hy
  have hd := (h.congr_of_eventuallyEq heq).deriv
  rw [hd]
  field_simp

theorem giantCell_log_deriv_bound : ∃ D : ℝ, 0 < D ∧ ∀ G p : ℝ,
    |p * deriv (giantCell G) p| ≤ D := by
  obtain ⟨M, hM, hb⟩ := smoothPartition_deriv_sub_bound
  have hφ (x : ℝ) : |deriv smoothPartition x| ≤ M + 1 := by
    calc
      _ = |(deriv smoothPartition x - smoothPartition x) + smoothPartition x| := by congr 1; ring
      _ ≤ |deriv smoothPartition x - smoothPartition x| + |smoothPartition x| := abs_add_le _ _
      _ ≤ M + 1 := add_le_add (hb x) (by rw [abs_of_nonneg (smoothPartition_nonneg x)]; exact smoothPartition_le_one x)
  refine ⟨M + 1, by positivity, ?_⟩
  intro G p
  by_cases hp : 0 < p
  · rw [giantCell_log_deriv G hp]
    exact hφ _
  · have hd : deriv (giantCell G) p = 0 :=
      ((hasDerivAt_const p (0 : ℝ)).congr_of_eventuallyEq
        (giantCell_eventually_zero G (le_of_not_gt hp))).deriv
    rw [hd, mul_zero, abs_zero]
    positivity

end Ostmann.Arithmetic

end OAI
