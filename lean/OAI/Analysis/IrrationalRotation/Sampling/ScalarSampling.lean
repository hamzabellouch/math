import OAI.Analysis.IrrationalRotation.Model.ScalarSampling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma delta_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ delta s := by
  exact le_min hs.1 (sub_nonneg.mpr hs.2)

lemma delta_le_half (s : ℝ) : delta s ≤ 1 / 2 := by
  unfold delta
  rcases le_total s (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

lemma cutoff_iff {α s : ℝ} : α ≤ delta s ↔ s ∈ Icc α (1 - α) := by
  simp only [delta, le_min_iff, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma rawKernel_nonneg {h α s t : ℝ} (hh : 0 ≤ h)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ rawKernel h α s t := by
  unfold rawKernel
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (mul_nonneg hh (delta_nonneg hs))) _
  · exact le_rfl

lemma integral_rawKernel (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    (∫ t : ℝ, rawKernel h α s t) = if α ≤ delta s then 1 else 0 := by
  unfold rawKernel
  split_ifs with hs
  · have hd : 0 < h * delta s := mul_pos hh (hα.trans_le hs)
    rw [integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le hd.le]
    simp only [sub_zero, smul_eq_mul]
    exact mul_inv_cancel₀ hd.ne'
  · simp

lemma integral_sq_rawKernel (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    (∫ t : ℝ, rawKernel h α s t ^ 2) =
      if α ≤ delta s then (h * delta s)⁻¹ else 0 := by
  unfold rawKernel
  split_ifs with hs
  · have hd : 0 < h * delta s := mul_pos hh (hα.trans_le hs)
    have heq : (fun t : ℝ => ((Ioo 0 (h * delta s)).indicator
        (fun _ => (h * delta s)⁻¹) t)^2) =
        (Ioo 0 (h * delta s)).indicator (fun _ => ((h * delta s)⁻¹)^2) := by
      funext t
      by_cases ht : t ∈ Ioo 0 (h * delta s) <;> simp [ht]
    rw [heq, integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le hd.le]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  · simp

lemma rawKernel_eq_zero_of_not_mem_unit {h α s t : ℝ}
    (_hh : 0 ≤ h) (hhone : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∉ Ioc (0 : ℝ) 1) : rawKernel h α s t = 0 := by
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro ht'
    apply ht
    refine ⟨ht'.1, ht'.2.le.trans ?_⟩
    calc
      h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone (delta_nonneg hs)
      _ ≤ 1 := by nlinarith [delta_le_half s]
  · rfl

theorem interval_integral_rawKernel {h α s : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rawKernel h α s t) =
      if α ≤ delta s then 1 else 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => rawKernel_eq_zero_of_not_mem_unit hh.le hhone hs ht)]
  exact integral_rawKernel h α s hh hα

theorem interval_integral_sq_rawKernel {h α s : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
      if α ≤ delta s then (h * delta s)⁻¹ else 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => by rw [rawKernel_eq_zero_of_not_mem_unit hh.le hhone hs ht]; norm_num)]
  exact integral_sq_rawKernel h α s hh hα

theorem integral_integral_rawKernel {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t) = 1 - 2 * α := by
  have heq : (fun s : ℝ => ∫ t : ℝ, rawKernel h α s t) =
      (Icc α (1 - α)).indicator (fun _ => (1 : ℝ)) := by
    funext s
    rw [integral_rawKernel h α s hh hα]
    simp only [cutoff_iff, Set.indicator_apply]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith : α ≤ 1 - α)]
    simp only [smul_eq_mul, mul_one]
    ring
  · intro s hs
    apply Set.indicator_of_notMem
    intro hs'
    apply hs
    exact ⟨hα.le.trans hs'.1, hs'.2.trans (by linarith)⟩

theorem integral_inv_delta {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in α..(1 - α), (delta s)⁻¹) =
      2 * Real.log (1 / (2 * α)) := by
  have hab : α ≤ 1 - α := by linarith
  have hmid : (1 / 2 : ℝ) ≤ 1 - α := by linarith
  have hd : Continuous (fun s : ℝ => delta s) :=
    continuous_id.min (continuous_const.sub continuous_id)
  have hfi : IntervalIntegrable (fun s : ℝ => (delta s)⁻¹) volume α (1 - α) := by
    apply intervalIntegral.intervalIntegrable_inv _ hd.continuousOn
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ne_of_gt (hα.trans_le (cutoff_iff.mpr hs))
  have hleft := hfi.mono_set (show uIcc α (1 / 2 : ℝ) ⊆ uIcc α (1 - α) by
    rw [uIcc_of_le hαhalf, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hmid)
  have hright := hfi.mono_set (show uIcc (1 / 2 : ℝ) (1 - α) ⊆ uIcc α (1 - α) by
    rw [uIcc_of_le hmid, uIcc_of_le hab]
    exact Icc_subset_Icc hαhalf le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hleftEq : (∫ s in α..(1 / 2 : ℝ), (delta s)⁻¹) =
      ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hαhalf] at hs
    change (min s (1 - s))⁻¹ = s⁻¹
    rw [min_eq_left (by linarith [hs.2] : s ≤ 1 - s)]
  have hrightEq : (∫ s in (1 / 2 : ℝ)..(1 - α), (delta s)⁻¹) =
      ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
    calc
      (∫ s in (1 / 2 : ℝ)..(1 - α), (delta s)⁻¹) =
          ∫ s in (1 / 2 : ℝ)..(1 - α), (1 - s)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hmid] at hs
        change (min s (1 - s))⁻¹ = (1 - s)⁻¹
        rw [min_eq_right (by linarith [hs.1] : 1 - s ≤ s)]
      _ = ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s⁻¹) 1]
        congr 1 <;> ring
  rw [hleftEq, hrightEq, integral_inv_of_pos hα (by norm_num : (0 : ℝ) < 1 / 2)]
  have heq : (1 / 2 : ℝ) / α = 1 / (2 * α) := by ring
  rw [heq]
  ring

theorem integral_integral_sq_rawKernel {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  have heq : (fun s : ℝ => ∫ t : ℝ, rawKernel h α s t ^ 2) =
      (Icc α (1 - α)).indicator (fun s => (h * delta s)⁻¹) := by
    funext s
    rw [integral_sq_rawKernel h α s hh hα]
    simp only [cutoff_iff, Set.indicator_apply]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : α ≤ 1 - α)]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_delta hα hαhalf]
    ring
  · intro s hs
    apply Set.indicator_of_notMem
    intro hs'
    apply hs
    exact ⟨hα.le.trans hs'.1, hs'.2.trans (by linarith)⟩

theorem double_interval_integral_rawKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t) = 1 - 2 * α := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t) =
        ∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [interval_integral_rawKernel hh hhone hα hs, integral_rawKernel h α s hh hα]
    _ = 1 - 2 * α := integral_integral_rawKernel hh hα hαhalf

theorem double_interval_integral_sq_rawKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
        ∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [interval_integral_sq_rawKernel hh hhone hα hs,
        integral_sq_rawKernel h α s hh hα]
    _ = (2 / h) * Real.log (1 / (2 * α)) := integral_integral_sq_rawKernel hh hα hαhalf

theorem interval_integral_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (z : ℝ) :
    (∫ v in (0 : ℝ)..1, circleKernel h α z v) =
      if α ≤ delta (Int.fract z) then 1 else 0 := by
  calc
    (∫ v in (0 : ℝ)..1, circleKernel h α z v) =
        ∫ v in (0 : ℝ)..1, rawKernel h α (Int.fract z) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = if α ≤ delta (Int.fract z) then 1 else 0 :=
      interval_integral_rawKernel hh hhone hα
        ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩

theorem double_interval_integral_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v) = 1 - 2 * α := by
  calc
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rawKernel h α z v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro z hz
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hz.1.le, hz.2⟩,
        Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = 1 - 2 * α := double_interval_integral_rawKernel hh hhone hα hαhalf

theorem double_interval_integral_sq_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  calc
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v ^ 2) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rawKernel h α z v ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro z hz
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hz.1.le, hz.2⟩,
        Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = (2 / h) * Real.log (1 / (2 * α)) :=
      double_interval_integral_sq_rawKernel hh hhone hα hαhalf

theorem averaged_circleKernel_bounds {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (z : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α z v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α z v) ≤ 1 := by
  rw [interval_integral_circleKernel hh hhone hα z]
  split_ifs <;> norm_num

theorem integral_sq_averaged_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α z v)^2) =
      1 - 2 * α := by
  calc
    (∫ z in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α z v)^2) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v := by
      apply intervalIntegral.integral_congr
      intro z _
      dsimp only
      rw [interval_integral_circleKernel hh hhone hα z]
      split_ifs <;> norm_num
    _ = 1 - 2 * α := double_interval_integral_circleKernel hh hhone hα hαhalf

lemma manuscript_parameters {m : ℕ} (hm : 200 ≤ m) :
    0 < (m : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      (m : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 ∧
      0 < 1 / (m : ℝ)^2 ∧ 1 / (m : ℝ)^2 ≤ 1 / 2 := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  refine ⟨Real.rpow_pos_of_pos hmp _,
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num),
    one_div_pos.mpr (sq_pos_of_pos hmp), ?_⟩
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by nlinarith)

theorem manuscriptKernel_mass {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m z v) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, mul_one_div] using
    double_interval_integral_circleKernel hh hhone hα hαhalf

theorem manuscriptKernel_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m z v ^ 2) =
      (2 / (m : ℝ) ^ (-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have heq : 1 / (2 * (1 / (m : ℝ)^2)) = (m : ℝ)^2 / 2 := by
    field_simp [hmR.ne']
  simpa only [manuscriptKernel, heq] using
    double_interval_integral_sq_circleKernel hh hhone hα hαhalf

lemma triangularKernel_sq (s t : ℝ) : triangularKernel s t ^ 2 = triangularKernel s t := by
  unfold triangularKernel
  by_cases ht : t ∈ Ioo 0 (1 - s) <;> simp [ht]

theorem interval_integral_triangularKernel {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, triangularKernel s t) = 1 - s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · unfold triangularKernel
    rw [integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le (sub_nonneg.mpr hs.2)]
    simp
  · intro t ht
    unfold triangularKernel
    apply Set.indicator_of_notMem
    intro ht'
    apply ht
    exact ⟨ht'.1, ht'.2.le.trans (by linarith [hs.1])⟩

theorem triangularKernel_mass :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, triangularKernel s t) = 1 / 2 := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, triangularKernel s t) =
        ∫ s in (0 : ℝ)..1, (1 - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact interval_integral_triangularKernel hs
    _ = 1 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      norm_num

theorem triangularKernel_secondMoment :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, triangularKernel s t ^ 2) = 1 / 2 := by
  simp_rw [triangularKernel_sq]
  exact triangularKernel_mass

theorem triangularKernel_averaged_secondMoment :
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, triangularKernel s t)^2) = 1 / 3 := by
  calc
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, triangularKernel s t)^2) =
        ∫ s in (0 : ℝ)..1, (1 - s)^2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      dsimp only
      rw [interval_integral_triangularKernel hs]
    _ = ∫ s in (0 : ℝ)..1, s^2 := by
      simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left (fun s : ℝ => s^2)
        (a := 0) (b := 1) 1
    _ = 1 / 3 := by norm_num

end Invariant233.ScalarSampling

end OAI
