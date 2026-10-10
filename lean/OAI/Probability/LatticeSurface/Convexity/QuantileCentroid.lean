import Mathlib
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

lemma intervalIntegrable_of_interior_bound {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Ioo a b))
    (hbound : ∀ x ∈ Ioo a b, |f x| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  apply IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) (hf.aestronglyMeasurable measurableSet_Ioo) C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs] using hbound x hx

lemma probability_velocity_bound {f : ℝ → ℝ} {a b C p : ℝ}
    (hf : IntervalDensity f a b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hvel : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p) (hp : p ∈ Ioo 0 1) :
    0 ≤ p*velocity f a b p ∧ p*velocity f a b p ≤ C := by
  constructor
  · exact mul_nonneg hp.1.le (velocity_pos hf hpos hab hp).le
  · have hh := (le_div_iff₀ hp.1).mp (hvel p hp)
    simpa only [mul_comm] using hh

lemma integrable_probability_velocity {f : ℝ → ℝ} {a b C : ℝ}
    (hf : IntervalDensity f a b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hvel : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p) :
    IntervalIntegrable (fun p => p*velocity f a b p) volume 0 1 := by
  apply intervalIntegrable_of_interior_bound (C := C) (by norm_num)
    (continuousOn_id.mul (continuousOn_velocity hf hpos hab))
  intro p hp
  have hh := probability_velocity_bound hf hab hpos hvel hp
  change |p*velocity f a b p| ≤ C
  simpa only [abs_of_nonneg hh.1] using hh.2

lemma integral_quantile_eq_firstMoment {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalDensity f a b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    (∫ p in (0:ℝ)..1, quantile f a b p) =
      (∫ x in a..b, x*f x) / (∫ x in a..b, f x) := by
  let M := ∫ x in a..b, f x
  have hM : 0 < M := integral_positive hf hpos hab
  have hi : IntervalIntegrable (fun x => x*f x) volume a b :=
    hf.integrable.continuousOn_mul continuousOn_id
  have hcq := quantile_continuousOn hf hpos hab
  have hcPrim : ContinuousOn (fun x => ∫ t in a..x, t*f t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval' hi (a := a) left_mem_uIcc)
  have hc : ContinuousOn (fun p => (∫ x in a..quantile f a b p, x*f x)/M) (Icc 0 1) :=
    (hcPrim.comp hcq (fun p hp => quantile_mem hf hpos hab hp)).div_const M
  have hd (p : ℝ) (hp : p ∈ Ioo 0 1) :
      HasDerivAt (fun p => (∫ x in a..quantile f a b p, x*f x)/M) (quantile f a b p) p := by
    have hq := quantile_mem_Ioo hf hpos hab hp
    have hiq : IntervalIntegrable (fun x => x*f x) volume a (quantile f a b p) := by
      apply hi.mono_set
      rw [uIcc_of_le hq.1.le, uIcc_of_le hab.le]
      exact Icc_subset_Icc_right hq.2.le
    have hcont : ContinuousAt (fun x => x*f x) (quantile f a b p) :=
      continuousAt_id.mul (hf.continuousAt hq)
    have hder := ((intervalIntegral.integral_hasDerivAt_right hiq
      ((continuousOn_id.mul hf.continuous).stronglyMeasurableAtFilter isOpen_Ioo _ hq)
      hcont).comp p (quantile_hasDerivAt hf hpos hab hp)).div_const M
    convert hder using 1 <;> try rfl
    field_simp [M, (integral_positive hf hpos hab).ne', (hpos _ hq).ne']
    rfl
  have hint : IntervalIntegrable (quantile f a b) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hcq
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ) ≤ 1) hc hd hint
  simpa only [quantile_right hf hpos hab, quantile_left hf hpos hab,
    intervalIntegral.integral_same, zero_div, sub_zero] using h

lemma integral_probability_velocity {f : ℝ → ℝ} {a b C : ℝ}
    (hf : IntervalDensity f a b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hvel : ∀ p ∈ Ioo 0 1, velocity f a b p ≤ C/p) :
    (∫ p in (0:ℝ)..1, p*velocity f a b p) =
      b - (∫ x in a..b, x*f x) / (∫ x in a..b, f x) := by
  have hcq := quantile_continuousOn hf hpos hab
  have hiq : IntervalIntegrable (quantile f a b) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hcq
  have hprim : ContinuousOn (fun p => ∫ t in (0:ℝ)..p, quantile f a b t) (Icc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (intervalIntegral.continuousOn_primitive_interval' hiq (a := 0) left_mem_uIcc)
  have hc : ContinuousOn (fun p => p*quantile f a b p-∫ t in (0:ℝ)..p, quantile f a b t)
      (Icc 0 1) := (continuousOn_id.mul hcq).sub hprim
  have hd (p : ℝ) (hp : p ∈ Ioo 0 1) :
      HasDerivAt (fun p => p*quantile f a b p-∫ t in (0:ℝ)..p, quantile f a b t)
        (p*velocity f a b p) p := by
    have hip : IntervalIntegrable (quantile f a b) volume 0 p := by
      apply hiq.mono_set
      rw [uIcc_of_le hp.1.le, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc_right hp.2.le
    have hh := ((hasDerivAt_id p).mul (quantile_hasDerivAt hf hpos hab hp)).sub
      (intervalIntegral.integral_hasDerivAt_right hip
        ((hcq.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo _ hp)
        (quantile_continuousAt hf hpos hab hp))
    convert hh using 1 <;> try rfl
    simp only [velocity, id_eq]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ) ≤ 1) hc hd (integrable_probability_velocity hf hab hpos hvel)
  simpa only [quantile_right hf hpos hab, one_mul, zero_mul,
    intervalIntegral.integral_same, sub_self, sub_zero,
    integral_quantile_eq_firstMoment hf hab hpos] using h

end SliceTransport

end

end OAI
