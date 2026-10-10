import OAI.Analysis.FiniteFactor.CrossedProduct.Rotation
import Mathlib.Probability.ConditionalProbability

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem sourceFract_measurable : Measurable (Int.fract : ℝ → ℝ) := by
  have hh := sourceCircleRepresentative_measurable.comp sourceCircle_mk_preserving.measurable
  simpa only [Function.comp_def, sourceCircleRepresentative_coe] using hh

/-- Every translated interval of length one maps to the same representative
Haar measure under fractional part. -/
theorem fract_unit_interval (a : ℝ) :
    (volume.restrict (Set.Ioc a (a+1))).map Int.fract = unitIntervalMeasure := by
  have hh := sourceCircleRepresentative_preserving.comp (AddCircle.measurePreserving_mk 1 a)
  have he : sourceCircleRepresentative ∘ ((↑) : ℝ → AddCircle (1 : ℝ)) = Int.fract := by
    funext x
    exact sourceCircleRepresentative_coe x
  simpa only [he] using hh.map_eq

theorem fract_integer_interval (a : ℝ) (n : ℕ) :
    (volume.restrict (Set.Ioc a (a+n))).map Int.fract = (n : ℝ≥0∞) • unitIntervalMeasure := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : Set.Ioc a (a+((n+1 : ℕ) : ℝ)) =
        Set.Ioc a (a+n) ∪ Set.Ioc (a+n) (a+n+1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)]
      congr 1
      push_cast
      ring
    rw [hu, Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add, ih, fract_unit_interval]
    · simp [add_smul]
    · exact sourceFract_measurable

/-- Periodizing normalized interval measure has density at most 1+1/length.
The bound is expressed as domination of measures on every measurable set. -/
theorem fract_interval_domination (a b : ℝ) (hab : a < b) :
    (cond volume (Set.Ioc a b)).map Int.fract ≤
      ENNReal.ofReal (1+1/(b-a)) • unitIntervalMeasure := by
  let n : ℕ := Nat.ceil (b-a)
  have hsub : Set.Ioc a b ⊆ Set.Ioc a (a+n) := by
    apply Set.Ioc_subset_Ioc le_rfl
    have hh : b-a ≤ (n : ℝ) := Nat.le_ceil _
    linarith
  have hle : (volume.restrict (Set.Ioc a b)).map Int.fract ≤
      (n : ℝ≥0∞) • unitIntervalMeasure := by
    rw [← fract_integer_interval a n]
    exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) sourceFract_measurable
  have hscalar : (ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞) ≤
      ENNReal.ofReal (1+1/(b-a)) := by
    have hpos : 0 < b-a := sub_pos.mpr hab
    have hn : (n : ℝ) < b-a+1 := Nat.ceil_lt_add_one hpos.le
    have hreal : (b-a)⁻¹ * (n : ℝ) ≤ 1+1/(b-a) := by
      apply (mul_le_mul_of_nonneg_left hn.le (inv_nonneg.mpr hpos.le)).trans_eq
      field_simp
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ sourceFract_measurable.aemeasurable, Real.volume_Ioc]
  calc
    _ ≤ (ENNReal.ofReal (b-a))⁻¹ • ((n : ℝ≥0∞) • unitIntervalMeasure) := by gcongr
    _ = ((ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞)) • unitIntervalMeasure := smul_smul _ _ _
    _ ≤ _ := by gcongr

/-- Positive scaling carries normalized interval measure to the normalized
scaled interval; this identifies the actual phase law before periodization. -/
theorem cond_interval_mul_pos (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    (cond volume (Set.Ioc a b)).map (fun t => c*t) =
      cond volume (Set.Ioc (c*a) (c*b)) := by
  have hp : (fun t : ℝ => c*t) ⁻¹' Set.Ioc (c*a) (c*b) = Set.Ioc a b := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, mul_lt_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hc]
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hclen : 0 < c*b-c*a := by nlinarith
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ (by fun_prop), Real.volume_Ioc, Real.volume_Ioc, ← hp,
    ← Measure.restrict_map (f := fun t : ℝ => c*t) (by fun_prop) measurableSet_Ioc,
    Real.map_volume_mul_left hc.ne', Measure.restrict_smul, smul_smul]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_inv_of_pos hlen,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hlen.le), ← ENNReal.ofReal_inv_of_pos hclen]
  congr 1
  field_simp

theorem cond_closed_interval_eq (a b : ℝ) :
    cond volume (Set.Icc a b) = cond volume (Set.Ioc a b) := by
  unfold ProbabilityTheory.cond
  rw [Real.volume_Icc, Real.volume_Ioc, ← restrict_Ioc_eq_restrict_Icc]

end
end FiniteFactor

end OAI
