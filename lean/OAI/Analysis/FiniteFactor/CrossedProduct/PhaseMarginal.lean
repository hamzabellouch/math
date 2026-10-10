import OAI.Analysis.FiniteFactor.CrossedProduct.AngleLaw
import OAI.Analysis.FiniteFactor.PeriodizedUniform

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem unitInterval_middle_compl (b : ℝ) (hb : 0 ≤ b) :
    unitIntervalMeasure (Set.Icc b (1-b))ᶜ ≤ ENNReal.ofReal (2*b) := by
  rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Icc.compl]
  have hsub : (Set.Icc b (1-b))ᶜ ∩ Set.Ico (0 : ℝ) 1 ⊆
      Set.Ico 0 b ∪ Set.Ioc (1-b) 1 := by
    intro x hx
    by_cases hxb : x < b
    · exact Or.inl ⟨hx.2.1,hxb⟩
    · exact Or.inr ⟨by by_contra hh; exact hx.1 ⟨le_of_not_gt hxb, le_of_not_gt hh⟩, hx.2.2.le⟩
  calc
    _ ≤ volume (Set.Ico 0 b ∪ Set.Ioc (1-b) 1) := measure_mono hsub
    _ ≤ volume (Set.Ico (0 : ℝ) b) + volume (Set.Ioc (1-b) 1) := measure_union_le _ _
    _ = ENNReal.ofReal (2*b) := by
      rw [Real.volume_Ico, Real.volume_Ioc]
      simp only [sub_zero, sub_sub_cancel]
      rw [← ENNReal.ofReal_add hb hb]
      congr 1
      ring

/-- The actual source-angle phase law has density at most five in the
second phase range. This is domination on all Borel sets. -/
theorem sourceAngle_positive_phase_domination (i : SourceCoordinate) (c : ℝ)
    (hc : 0 < c) (hlen : 1/4 ≤ c*sourceAngleUnit i) :
    (sourceAngleMarginal i).map (fun t => Int.fract (c*t)) ≤
      (5 : ℝ≥0∞) • unitIntervalMeasure := by
  have ha := sourceAngleUnit_pos i
  have he : (sourceAngleMarginal i).map (fun t => Int.fract (c*t)) =
      (cond volume (Set.Ioc (c*sourceAngleUnit i) (c*(2*sourceAngleUnit i)))).map Int.fract := by
    rw [← cond_interval_mul_pos (sourceAngleUnit i) (2*sourceAngleUnit i) c (by linarith) hc,
      Measure.map_map sourceFract_measurable (by fun_prop)]
    rw [sourceAngleMarginal, sourceAngleInterval, cond_closed_interval_eq]
    rfl
  rw [he]
  have hpos : c*sourceAngleUnit i < c*(2*sourceAngleUnit i) := by nlinarith
  apply (fract_interval_domination _ _ hpos).trans
  have hh : 1+1/(c*(2*sourceAngleUnit i)-c*sourceAngleUnit i) ≤ (5 : ℝ) := by
    have heq : c*(2*sourceAngleUnit i)-c*sourceAngleUnit i = c*sourceAngleUnit i := by ring
    rw [heq]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/4) hlen
    have hh' : 1/(c*sourceAngleUnit i) ≤ 4 := by
      simpa [one_div, mul_inv_rev] using hh
    linarith
  have hscalar : ENNReal.ofReal (1+1/(c*(2*sourceAngleUnit i)-c*sourceAngleUnit i)) ≤ 5 := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  gcongr

/-- Reflection preserves the symmetric phase eligibility interval, including
integer phases at the cut. -/
theorem fract_neg_middle_iff (b t : ℝ) :
    Int.fract (-t) ∈ Set.Icc b (1-b) ↔ Int.fract t ∈ Set.Icc b (1-b) := by
  by_cases ht : Int.fract t = 0
  · rw [Int.fract_neg_eq_zero.mpr ht, ht]
  · rw [Int.fract_neg ht]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem threshold_middle_iff (b t : ℝ) :
    1-Int.fract t ∈ Set.Icc b (1-b) ↔ Int.fract t ∈ Set.Icc b (1-b) := by
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

/-- Proposition phases' one-coordinate miss bound, valid for both signs and
for every coordinate in the actual source interval. -/
theorem sourceAngle_phase_miss (i : SourceCoordinate) (k : ℤ) (b : ℝ) (hb : 0 ≤ b)
    (hk : ((sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K)/4 ≤ |(k : ℝ)|) :
    sourceAngleMarginal i {t | 1-Int.fract ((k : ℝ)*t) ∉ Set.Icc b (1-b)} ≤
      ENNReal.ofReal (10*b) := by
  have hN := mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)
  have hkpos : 0 < |(k : ℝ)| := lt_of_lt_of_le (by positivity) hk
  have hlen : 1/4 ≤ |(k : ℝ)| *sourceAngleUnit i := by
    unfold sourceAngleUnit
    rw [mul_one_div]
    apply (le_div_iff₀ hN).mpr
    nlinarith [hk]
  have he : {t : ℝ | 1-Int.fract ((k : ℝ)*t) ∉ Set.Icc b (1-b)} =
      (fun t : ℝ => Int.fract (|(k : ℝ)| *t)) ⁻¹' (Set.Icc b (1-b))ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, threshold_middle_iff]
    rcases le_total 0 (k : ℝ) with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_nonpos hneg, neg_mul, fract_neg_middle_iff]
  rw [he, ← Measure.map_apply (f := fun t : ℝ => Int.fract (|(k : ℝ)| *t))
    (by exact sourceFract_measurable.comp (by fun_prop)) measurableSet_Icc.compl]
  calc
    _ ≤ ((5 : ℝ≥0∞) • unitIntervalMeasure) (Set.Icc b (1-b))ᶜ :=
      sourceAngle_positive_phase_domination i |(k : ℝ)| hkpos hlen _
    _ = 5 * unitIntervalMeasure (Set.Icc b (1-b))ᶜ := rfl
    _ ≤ 5 * ENNReal.ofReal (2*b) := by
      have hh := unitInterval_middle_compl b hb
      gcongr
    _ = ENNReal.ofReal (10*b) := by
      rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      congr 1
      ring

end
end FiniteFactor

end OAI
