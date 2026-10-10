import OAI.Analysis.FiniteFactor.Sampling.TestedFirstMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Squaring the constant-height slice leaves its reciprocal interval length. -/
theorem samplingWeight_square_slice (h α s : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    (∫ t, samplingWeight false h α s t ^ 2 ∂unitIntervalMeasure) =
      if α ≤ samplingDistance s then 1/(h*samplingDistance s) else 0 := by
  have he : (fun t => samplingWeight false h α s t ^ 2) =
      fun t => (1/(h*samplingDistance s))*samplingWeight false h α s t := by
    funext t
    unfold samplingWeight
    simp only [Bool.false_eq_true,ite_false]
    split_ifs <;> ring
  rw [he,integral_const_mul,samplingWeight_first_integral false h α s hh hh1 hα hs]
  simp only [Bool.false_eq_true,ite_false]
  split_ifs <;> simp

/-- Exact logarithmic integral of the cutoff reciprocal distance. -/
theorem samplingDistance_cutoff_integral (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, (if α ≤ samplingDistance s then (samplingDistance s)⁻¹ else 0)
      ∂unitIntervalMeasure) = 2*Real.log (1/(2*α)) := by
  have hab : α ≤ 1-α := by linarith
  have hset : {s | α ≤ samplingDistance s} = Set.Icc α (1-α) := by
    ext s
    simp only [Set.mem_ofPred_eq,samplingDistance,le_min_iff,Set.mem_Icc]
    constructor <;> intro hs <;> constructor <;> linarith [hs.1,hs.2]
  have he : (fun s => if α ≤ samplingDistance s then (samplingDistance s)⁻¹ else 0) =
      (Set.Icc α (1-α)).indicator (fun s => (samplingDistance s)⁻¹) := by
    rw [← hset]
    rfl
  rw [he,integral_indicator measurableSet_Icc]
  unfold unitIntervalMeasure
  rw [Measure.restrict_restrict measurableSet_Icc,Set.inter_eq_left.mpr (show
    Set.Icc α (1-α) ⊆ Set.Ico (0 : ℝ) 1 from fun s hs => ⟨hα.le.trans hs.1,by linarith [hs.2]⟩),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
  have hc : ContinuousOn (fun s => (samplingDistance s)⁻¹) (Set.Icc α (1-α)) := by
    apply ContinuousOn.inv₀ (by unfold samplingDistance; fun_prop)
    intro s hs
    have hd : 0 < samplingDistance s := lt_min (hα.trans_le hs.1) (by linarith [hs.2])
    exact hd.ne'
  have hi : IntervalIntegrable (fun s => (samplingDistance s)⁻¹) volume α (1-α) := hc.intervalIntegrable_of_Icc hab
  have hleft : IntervalIntegrable (fun s => (samplingDistance s)⁻¹) volume α (1/2) :=
    hi.mono_set (by rw [Set.uIcc_of_le hα1,Set.uIcc_of_le hab]; intro s hs; exact ⟨hs.1,by linarith [hs.2]⟩)
  have hright : IntervalIntegrable (fun s => (samplingDistance s)⁻¹) volume (1/2) (1-α) :=
    hi.mono_set (by rw [Set.uIcc_of_le (show (1/2 : ℝ) ≤ 1-α by linarith),Set.uIcc_of_le hab]; intro s hs; exact ⟨by linarith [hs.1],hs.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hl : (∫ s in α..(1/2 : ℝ), (samplingDistance s)⁻¹) = Real.log ((1/2)/α) := by
    calc
      _ = ∫ s in α..(1/2 : ℝ), s⁻¹ := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hα1]
        intro s hs
        change (min s (1-s))⁻¹ = s⁻¹
        rw [min_eq_left (by linarith [hs.2])]
      _ = _ := integral_inv_of_pos hα (by norm_num)
  have hr : (∫ s in (1/2 : ℝ)..(1-α), (samplingDistance s)⁻¹) = Real.log ((1/2)/α) := by
    calc
      _ = ∫ s in (1/2 : ℝ)..(1-α), (1-s)⁻¹ := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (show (1/2 : ℝ) ≤ 1-α by linarith)]
        intro s hs
        change (min s (1-s))⁻¹ = (1-s)⁻¹
        rw [min_eq_right (by linarith [hs.1])]
      _ = ∫ s in α..(1/2 : ℝ), s⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s⁻¹) 1]
        norm_num
      _ = _ := integral_inv_of_pos hα (by norm_num)
  rw [hl,hr,show (1/2 : ℝ)/α = 1/(2*α) by ring]
  ring

theorem samplingWeight_square_integral (h α : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, ∫ t, samplingWeight false h α s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) = (2/h)*Real.log (1/(2*α)) := by
  calc
    _ = ∫ s, (1/h)*(if α ≤ samplingDistance s then (samplingDistance s)⁻¹ else 0)
        ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [show ∀ᵐ s ∂unitIntervalMeasure, s ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with s hs
      rw [samplingWeight_square_slice h α s hh hh1 hα hs]
      split_ifs <;> simp [div_eq_mul_inv,mul_comm]
    _ = _ := by
      rw [integral_const_mul,samplingDistance_cutoff_integral α hα hα1]
      ring

end
end FiniteFactor

end OAI
