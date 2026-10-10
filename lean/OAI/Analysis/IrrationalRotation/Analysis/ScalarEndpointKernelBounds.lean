import OAI.Analysis.IrrationalRotation.Analysis.EndpointKernelGeometry
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem measurable_rawKernel_pair (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => rawKernel h α p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => delta p.1) :=
    (continuous_fst.min (continuous_const.sub continuous_fst)).measurable
  unfold rawKernel
  simp only [Set.indicator_apply, mem_Ioo]
  apply Measurable.ite (measurableSet_le measurable_const hd)
  · apply Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.mul hd)))
    · exact (measurable_const.mul hd).inv
    · exact measurable_const
  · exact measurable_const

theorem measurable_circleEndpoint_pair (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => circleKernel h α (p.1 - p.2) p.2) := by
  exact (measurable_rawKernel_pair h α).comp
    (((measurable_fst.sub measurable_snd).fract).prodMk measurable_snd.fract)

theorem rawKernel_height {h α s v : ℝ} (hh : 0 < h) (hα : 0 < α) :
    0 ≤ rawKernel h α s v ∧ rawKernel h α s v ≤ (h * α)⁻¹ := by
  unfold rawKernel
  split_ifs with hd
  · by_cases hv : v ∈ Ioo 0 (h * delta s)
    · rw [Set.indicator_of_mem hv]
      have hp : 0 < h * delta s := mul_pos hh (hα.trans_le hd)
      exact ⟨(inv_pos.mpr hp).le, inv_anti₀ (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hd hh.le)⟩
    · rw [Set.indicator_of_notMem hv]
      exact ⟨le_rfl, (inv_pos.mpr (mul_pos hh hα)).le⟩
  · exact ⟨le_rfl, (inv_pos.mpr (mul_pos hh hα)).le⟩

theorem circleEndpoint_intervalIntegrable {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (s : ℝ) : IntervalIntegrable (fun v => circleKernel h α (s - v) v) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((measurable_circleEndpoint_pair h α).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable ((h * α)⁻¹)
  apply Filter.Eventually.of_forall
  intro v
  change ‖circleKernel h α (s - v) v‖ ≤ _
  unfold circleKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (rawKernel_height hh hα).1]
  exact (rawKernel_height hh hα).2

theorem delta_backward_bound {s v : ℝ} (hv : 0 ≤ v) : delta s ≤ delta (s - v) + v := by
  have heq : delta (s - v) + v = min s (1 - s + 2 * v) := by
    unfold delta
    rw [← min_add_add_right]
    congr 1 <;> ring
  rw [heq]
  exact min_le_min le_rfl (by linarith)

theorem uncut_rawEndpoint_height {h s v : ℝ} (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s < 1) (hv : 0 ≤ v) :
    0 ≤ rawKernel h 0 (s - v) v ∧
      rawKernel h 0 (s - v) v ≤ (1 + h) / (h * delta s) := by
  have hdS : 0 < delta s := lt_min hs0 (by linarith)
  have hC : 0 ≤ (1 + h) / (h * delta s) := by positivity
  unfold rawKernel
  split_ifs with hd
  · by_cases hmem : v ∈ Ioo 0 (h * delta (s - v))
    · rw [Set.indicator_of_mem hmem]
      have hdpos : 0 < delta (s - v) := by
        have hp : 0 < h * delta (s - v) := lt_trans hmem.1 hmem.2
        exact (mul_pos_iff_of_pos_left hh).mp hp
      refine ⟨(inv_pos.mpr (mul_pos hh hdpos)).le, ?_⟩
      have hcomp : delta s ≤ (1 + h) * delta (s - v) := by
        have := delta_backward_bound (s := s) hv
        linarith [hmem.2]
      rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos hh hdpos) (mul_pos hh hdS)]
      nlinarith [mul_le_mul_of_nonneg_left hcomp hh.le]
    · rw [Set.indicator_of_notMem hmem]
      exact ⟨le_rfl, hC⟩
  · exact ⟨le_rfl, hC⟩

theorem uncut_rawEndpoint_intervalIntegrable {h s : ℝ} (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun v => rawKernel h 0 (s - v) v) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((measurable_rawKernel_pair h 0).comp
      ((measurable_const.sub measurable_id).prodMk measurable_id)).aestronglyMeasurable
    ((1 + h) / (h * delta s))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  change ‖rawKernel h 0 (s - v) v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (uncut_rawEndpoint_height hh hs0 hs1 hv.1.le).1]
  exact (uncut_rawEndpoint_height hh hs0 hs1 hv.1.le).2

theorem uncut_circleEndpoint_intervalIntegrable {h s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun v => circleKernel h 0 (s - v) v) volume 0 1 := by
  apply (uncut_rawEndpoint_intervalIntegrable hh hs0 hs1).congr_uIoo
  intro v hv
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  exact (uncut_endpoint_no_wrap hh.le hh1 hs0 hs1 hv.1 hv.2).symm

theorem circleEndpoint_average_le_density {h α s : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs0 : 0 < s) (hs1 : s < 1) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤
        ScalarEndpointDensity.averagedDensity h s := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro v _
    exact (rawKernel_height hh0 hα).1
  · rw [← integral_uncut_circleEndpoint hh0 hh1 hs0 hs1]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (circleEndpoint_intervalIntegrable hh0 hα s)
      (uncut_circleEndpoint_intervalIntegrable hh0 hh1.le hs0 hs1)
    intro v _
    exact rawKernel_le_uncut hh0.le
      ⟨Int.fract_nonneg (s - v), (Int.fract_lt_one (s - v)).le⟩

theorem stronglyMeasurable_circleEndpoint_average (h α : ℝ) :
    StronglyMeasurable (fun s => ∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) := by
  have hm := (measurable_circleEndpoint_pair h α).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hm

theorem circleEndpoint_average_height {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤ (h * α)⁻¹ := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro v _
    exact (rawKernel_height hh hα).1
  · calc
      _ ≤ ∫ _v in (0 : ℝ)..1, (h * α)⁻¹ :=
        intervalIntegral.integral_mono_on (by norm_num)
          (circleEndpoint_intervalIntegrable hh hα s) intervalIntegrable_const
          (fun _ _ => (rawKernel_height hh hα).2)
      _ = _ := by simp

theorem intervalIntegrable_square_of_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1)))
    (hC : 0 ≤ C) (hb : ∀ s ∈ Ioo (0 : ℝ) 1, |f s| ≤ C) :
    IntervalIntegrable (fun s => (f s) ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    (hf.pow 2) (C ^ 2)
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hne] with s hs hne
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hbound := hb s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
  change ‖(f s) ^ 2‖ ≤ C ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hbound)

theorem circleEndpoint_averaged_secondMoment {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v)^2) ≤
      1 + h^2 / (1 - h)^2 := by
  have hcut : IntervalIntegrable
      (fun s => (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v)^2) volume 0 1 := by
    apply intervalIntegrable_square_of_bound
      (stronglyMeasurable_circleEndpoint_average h α).aestronglyMeasurable
      (show 0 ≤ (h * α)⁻¹ by positivity)
    intro s _
    rw [abs_of_nonneg (circleEndpoint_average_height hh0 hα s).1]
    exact (circleEndpoint_average_height hh0 hα s).2
  have huncut : IntervalIntegrable
      (fun s => (ScalarEndpointDensity.averagedDensity h s)^2) volume 0 1 := by
    apply intervalIntegrable_square_of_bound
      (ScalarEndpointDensity.averagedDensity_intervalIntegrable hh0 hh1).def'.aestronglyMeasurable
      (show 0 ≤ (1 - h)⁻¹ by positivity)
    intro s _
    rw [abs_of_nonneg (ScalarEndpointDensity.averagedDensity_nonneg hh0 hh1 s)]
    exact ScalarEndpointDensity.averagedDensity_upper hh0 hh1 s
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, (ScalarEndpointDensity.averagedDensity h s)^2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hcut huncut
      intro s hs
      have hp := circleEndpoint_average_le_density hh0 hh1 hα hs.1 hs.2
      exact (sq_le_sq₀ hp.1 (ScalarEndpointDensity.averagedDensity_nonneg hh0 hh1 s)).mpr hp.2
    _ ≤ _ := ScalarEndpointDensity.averagedDensity_second_moment hh0 hh1

theorem manuscriptEndpointKernel_averaged_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hh1 : (m : ℝ)^(-(3 / 5 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hm1 (by norm_num)
  exact circleEndpoint_averaged_secondMoment hh hh1 hα

theorem circleEndpoint_periodize (h α s v : ℝ) :
    circleKernel h α (Int.fract s - v) v = circleKernel h α (s - v) v := by
  unfold circleKernel
  congr 1
  calc
    Int.fract (Int.fract s - v) = Int.fract ((s - v) - (⌊s⌋ : ℝ)) := by
      congr 1
      unfold Int.fract
      ring
    _ = _ := Int.fract_sub_intCast _ _

theorem circleEndpoint_at_zero {h α v : ℝ} (_hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hv0 : 0 < v) (hv1 : v < 1) : circleKernel h α (0 - v) v = 0 := by
  have hfract : Int.fract (-v) = 1 - v := by
    rw [Int.fract_neg (by rw [Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]; exact hv0.ne'),
      Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  unfold circleKernel
  rw [zero_sub, hfract, Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro hv
    have hd0 : 0 ≤ delta (1 - v) := delta_nonneg ⟨by linarith, by linarith⟩
    have hd : delta (1 - v) ≤ v := by
      unfold delta
      exact (min_le_right _ _).trans (by linarith)
    have hm : h * delta (1 - v) ≤ delta (1 - v) :=
      (mul_le_mul_of_nonneg_right hh1 hd0).trans_eq (one_mul _)
    linarith [hv.2]
  · rfl

theorem integral_circleEndpoint_at_zero {h α : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h α (0 - v) v) = 0 := by
  calc
    _ = ∫ _v in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact circleEndpoint_at_zero hh0 hh1 hv.1 hv.2
    _ = _ := by simp

theorem circleEndpoint_average_uniform_bound {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤ (1 - h)⁻¹ := by
  refine ⟨(circleEndpoint_average_height hh0 hα s).1, ?_⟩
  have heq : (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) =
      ∫ v in (0 : ℝ)..1, circleKernel h α (Int.fract s - v) v := by
    apply intervalIntegral.integral_congr
    intro v _
    exact (circleEndpoint_periodize h α s v).symm
  rw [heq]
  by_cases hs : Int.fract s = 0
  · rw [hs, integral_circleEndpoint_at_zero hh0.le hh1.le]
    positivity
  · have hs0 : 0 < Int.fract s := lt_of_le_of_ne (Int.fract_nonneg s) (Ne.symm hs)
    exact (circleEndpoint_average_le_density hh0 hh1 hα hs0 (Int.fract_lt_one s)).2.trans
      (ScalarEndpointDensity.averagedDensity_upper hh0 hh1 _)

theorem manuscript_width_le_half {m : ℕ} (hm : 200 ≤ m) :
    (m : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 / 2 := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (by omega : 4 ≤ m)
  calc
    _ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hm4 (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
      norm_num

theorem manuscriptEndpointKernel_averaged_bounds {m : ℕ} (hm : 200 ≤ m) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v) ∧
      (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v) ≤ 2 := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hhalf := manuscript_width_le_half hm
  have hh1 : (m : ℝ)^(-(3 / 5 : ℝ)) < 1 := by linarith
  have hb := circleEndpoint_average_uniform_bound hh hh1 hα s
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 2 := by norm_num

end Invariant233.ScalarSampling

end OAI
