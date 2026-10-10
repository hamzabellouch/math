import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # The Hausdorff-dimension lower bound of the actual Frostman law -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem frostman_set_bound (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (A : Set (Space d)) :
    (μ : Measure (Space d)) A ≤ ENNReal.ofReal (C*2^s) * (Metric.ediam A)^s := by
  let := noAtoms_of_frostman (μ : Measure (Space d)) hs hfrost
  have hK : 0 < C*2^s := mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx⟩ := hA
    by_cases hzero : Metric.ediam A = 0
    · rw [hzero,ENNReal.zero_rpow_of_pos hs,mul_zero]
      apply le_of_eq
      apply measure_mono_null _ (measure_singleton x)
      intro y hy
      exact Set.mem_singleton_iff.mpr ((Metric.ediam_eq_zero_iff.mp hzero) hy hx)
    by_cases htop : Metric.ediam A = ∞
    · rw [htop,ENNReal.top_rpow_of_pos hs,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hK)]
      exact le_top
    let r := (Metric.ediam A).toReal
    have hr : 0 < r := ENNReal.toReal_pos hzero htop
    have hsub : A ⊆ ball x (2*r) := by
      intro y hy
      have hd : dist y x ≤ r := by
        have hd := ENNReal.toReal_mono htop (Metric.edist_le_ediam_of_mem hy hx)
        simpa only [edist_dist,ENNReal.toReal_ofReal dist_nonneg] using hd
      exact lt_of_le_of_lt hd (by linarith)
    calc
      (μ : Measure (Space d)) A ≤ ENNReal.ofReal (C*(2*r)^s) :=
        (measure_mono hsub).trans (hfrost x (2*r) (by positivity))
      _ = ENNReal.ofReal (C*2^s) * (Metric.ediam A)^s := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le,← mul_assoc,
          ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_rpow_of_pos hr]
        congr 1
        exact congrArg (fun z : ℝ≥0∞ => z^s) (ENNReal.ofReal_toReal htop)
  · rw [Set.not_nonempty_iff_eq_empty.mp hA,measure_empty]
    exact zero_le

theorem frostman_dimension_lower (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ENNReal.ofReal s ≤ dimH (μ : Measure (Space d)).support := by
  let K := ENNReal.ofReal (C*2^s)
  have hK : K ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeasure : K⁻¹ • (μ : Measure (Space d)) ≤ Measure.hausdorffMeasure s := by
    apply Measure.le_hausdorffMeasure s _ ∞ (by simp)
    intro A _
    rw [Measure.smul_apply,smul_eq_mul]
    calc
      K⁻¹ * (μ : Measure (Space d)) A ≤ K⁻¹ * (K*(Metric.ediam A)^s) :=
        mul_le_mul_right (frostman_set_bound μ hs hC hfrost A) _
      _ = (Metric.ediam A)^s := by rw [← mul_assoc,ENNReal.inv_mul_cancel hK hKtop,one_mul]
  have hsup : (μ : Measure (Space d)) (μ : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  have hpositive : 0 < (K⁻¹ • (μ : Measure (Space d))) (μ : Measure (Space d)).support := by
    rw [Measure.smul_apply,smul_eq_mul,hsup,mul_one]
    exact pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr hKtop)
  have hnonzero : Measure.hausdorffMeasure s (μ : Measure (Space d)).support ≠ 0 :=
    (hpositive.trans_le (hmeasure _)).ne'
  rw [ENNReal.ofReal_eq_coe_nnreal hs.le]
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨s,hs.le⟩) hnonzero

end Falconer

end OAI
