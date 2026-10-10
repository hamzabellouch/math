import OAI.Analysis.FiniteFactor.PeriodizedUniform
import OAI.Analysis.FiniteFactor.CrossedProduct.AngleLaw
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Lower counterpart to periodized interval domination; the floor-length
subinterval contributes exact Haar measure. -/
theorem fract_interval_lower (a b : ℝ) (hab : a < b) :
    ENNReal.ofReal (1-1/(b-a)) • unitIntervalMeasure ≤
      (cond volume (Set.Ioc a b)).map Int.fract := by
  let n : ℕ := Nat.floor (b-a)
  have hpos : 0 < b-a := sub_pos.mpr hab
  have hsub : Set.Ioc a (a+n) ⊆ Set.Ioc a b := by
    apply Set.Ioc_subset_Ioc le_rfl
    have hh : (n : ℝ) ≤ b-a := Nat.floor_le hpos.le
    linarith
  have hle : (n : ℝ≥0∞) • unitIntervalMeasure ≤
      (volume.restrict (Set.Ioc a b)).map Int.fract := by
    rw [← fract_integer_interval a n]
    exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) sourceFract_measurable
  have hscalar : ENNReal.ofReal (1-1/(b-a)) ≤
      (ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞) := by
    have hn : b-a < (n : ℝ)+1 := Nat.lt_floor_add_one (b-a)
    have hreal : 1-1/(b-a) ≤ (b-a)⁻¹ * (n : ℝ) := by
      apply (le_inv_mul_iff₀ hpos).mpr
      field_simp
      linarith
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ sourceFract_measurable.aemeasurable, Real.volume_Ioc]
  calc
    _ ≤ ((ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞)) • unitIntervalMeasure := by gcongr
    _ = (ENNReal.ofReal (b-a))⁻¹ • ((n : ℝ≥0∞) • unitIntervalMeasure) :=
      (smul_smul _ _ _).symm
    _ ≤ _ := by gcongr

/-- Two-sided near-uniformity for the actual single-phase law, on every
Borel set. The error is exactly 1/(n times the source interval length). -/
theorem sourceAngle_phase_sandwich (i : SourceCoordinate) (n : ℝ) (hn : 0 < n) :
    ENNReal.ofReal (1-1/(n*sourceAngleUnit i)) • unitIntervalMeasure ≤
      (sourceAngleMarginal i).map (fun t => Int.fract (n*t)) ∧
    (sourceAngleMarginal i).map (fun t => Int.fract (n*t)) ≤
      ENNReal.ofReal (1+1/(n*sourceAngleUnit i)) • unitIntervalMeasure := by
  have ha := sourceAngleUnit_pos i
  have he : (sourceAngleMarginal i).map (fun t => Int.fract (n*t)) =
      (cond volume (Set.Ioc (n*sourceAngleUnit i) (n*(2*sourceAngleUnit i)))).map Int.fract := by
    rw [← cond_interval_mul_pos (sourceAngleUnit i) (2*sourceAngleUnit i) n (by linarith) hn,
      Measure.map_map sourceFract_measurable (by fun_prop)]
    rw [sourceAngleMarginal, sourceAngleInterval, cond_closed_interval_eq]
    rfl
  rw [he]
  have hpos : n*sourceAngleUnit i < n*(2*sourceAngleUnit i) := by nlinarith
  have hlen : n*(2*sourceAngleUnit i)-n*sourceAngleUnit i = n*sourceAngleUnit i := by ring
  constructor
  · simpa only [hlen] using fract_interval_lower _ _ hpos
  · simpa only [hlen] using fract_interval_domination _ _ hpos

/-- Nonnegative tests inherit the exact relative error from a measure sandwich. -/
theorem integral_error_of_measure_sandwich {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hlo : ENNReal.ofReal (1-ε) • μ ≤ ν)
    (hhi : ν ≤ ENNReal.ofReal (1+ε) • μ)
    (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g μ) :
    Integrable g ν ∧ |(∫ x, g x ∂ν) - ∫ x, g x ∂μ| ≤ ε * ∫ x, g x ∂μ := by
  have hgui := hgi.smul_measure (c := ENNReal.ofReal (1+ε)) ENNReal.ofReal_ne_top
  have hgν := hgui.mono_measure hhi
  refine ⟨hgν, ?_⟩
  have hl := integral_mono_measure hlo (Filter.Eventually.of_forall hg) hgν
  have hu := integral_mono_measure hhi (Filter.Eventually.of_forall hg) hgui
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hl
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hu
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The source's single-phase test estimate for all integrable nonnegative
weights, not merely for rectangle indicators. -/
theorem sourceAngle_single_phase_test (i : SourceCoordinate) (n : ℝ) (hn : 0 < n)
    (hlen : 1 ≤ n*sourceAngleUnit i) (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hgm : Measurable g) (hgi : Integrable g unitIntervalMeasure) :
    |(∫ t, g (Int.fract (n*t)) ∂sourceAngleMarginal i) -
        ∫ t, g t ∂unitIntervalMeasure| ≤
      (1/(n*sourceAngleUnit i)) * ∫ t, g t ∂unitIntervalMeasure := by
  have hp := sourceAngle_phase_sandwich i n hn
  have he0 : 0 ≤ 1/(n*sourceAngleUnit i) := by positivity
  have he1 : 1/(n*sourceAngleUnit i) ≤ 1 := by
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlen).trans_eq (by norm_num)
  have hh := (integral_error_of_measure_sandwich unitIntervalMeasure _ _ he0 he1 hp.1 hp.2 g hg hgi).2
  have hphase : Measurable (fun t : ℝ => Int.fract (n*t)) :=
    sourceFract_measurable.comp (measurable_const.mul measurable_id)
  rw [integral_map hphase.aemeasurable hgm.aestronglyMeasurable] at hh
  exact hh

end
end FiniteFactor

end OAI
