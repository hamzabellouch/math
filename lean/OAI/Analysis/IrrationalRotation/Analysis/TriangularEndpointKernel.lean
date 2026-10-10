import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEndpointVariation

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem endpoint_triangularKernel_eq_indicator {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (t : ℝ) :
    triangularKernel (Int.fract (s - t)) t = (Ioc 0 s).indicator (fun _ => 1) t := by
  have hsupport : t ∈ Ioo 0 (1 - Int.fract (s - t)) ↔ t ∈ Ioc 0 s := by
    constructor
    · intro ht
      refine ⟨ht.1, ?_⟩
      by_contra hts
      have hst : s < t := lt_of_not_ge hts
      have htone : t < 1 := by linarith [ht.2, Int.fract_nonneg (s - t)]
      have hfrac : Int.fract (s - t) = s - t + 1 := by
        rw [← Int.fract_add_one (s - t)]
        exact Int.fract_eq_self.mpr ⟨by linarith [hs.1], by linarith⟩
      rw [hfrac] at ht
      linarith [hs.1, ht.2]
    · intro ht
      have hfrac : Int.fract (s - t) = s - t :=
        Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht.2, by linarith [hs.2, ht.1]⟩
      rw [mem_Ioo, hfrac]
      exact ⟨ht.1, by linarith [hs.2]⟩
  simp only [triangularKernel, Set.indicator_apply, hsupport]

theorem interval_integral_endpoint_triangularKernel {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, triangularKernel (Int.fract (s - t)) t) = s := by
  simp_rw [endpoint_triangularKernel_eq_indicator hs]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator_const _ measurableSet_Ioc,
      Real.volume_real_Ioc_of_le hs.1]
    simp
  · intro t ht
    apply Set.indicator_of_notMem
    intro hts
    exact ht ⟨hts.1, hts.2.trans hs.2.le⟩

theorem endpoint_triangularKernel_fract (s t : ℝ) :
    triangularKernel (Int.fract (s - t)) t =
      triangularKernel (Int.fract (Int.fract s - t)) t := by
  have heq : Int.fract s - t = (s - t) - (⌊s⌋ : ℤ) := by
    rw [Int.fract]
    ring
  simp only [heq, Int.fract_sub_intCast]

theorem interval_integral_endpoint_triangularKernel_periodic (s : ℝ) :
    (∫ t in (0 : ℝ)..1, triangularKernel (Int.fract (s - t)) t) = Int.fract s := by
  simp_rw [endpoint_triangularKernel_fract s]
  exact interval_integral_endpoint_triangularKernel
    ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩

theorem endpoint_triangularKernel_mass :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      triangularKernel (Int.fract (s - t)) t) = 1 / 2 := by
  calc
    _ = ∫ s in (0 : ℝ)..1, s := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro s hs
      exact interval_integral_endpoint_triangularKernel ⟨hs.1.le, hs.2⟩
    _ = 1 / 2 := by norm_num

theorem endpoint_triangularKernel_secondMoment :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      triangularKernel (Int.fract (s - t)) t ^ 2) = 1 / 2 := by
  simp_rw [triangularKernel_sq]
  exact endpoint_triangularKernel_mass

theorem endpoint_triangularKernel_averaged_secondMoment :
    (∫ s in (0 : ℝ)..1,
      (∫ t in (0 : ℝ)..1, triangularKernel (Int.fract (s - t)) t) ^ 2) = 1 / 3 := by
  calc
    _ = ∫ s in (0 : ℝ)..1, s ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro s hs
      dsimp only
      rw [interval_integral_endpoint_triangularKernel ⟨hs.1.le, hs.2⟩]
    _ = 1 / 3 := by norm_num

private theorem lower_interval_control (s : ℝ) :
    VariationControl ((Ioc 0 s).indicator (fun _ => (1 : ℝ))) 1 2 := by
  have hstep : VariationControl (fun t : ℝ => if 0 < t then 1 else 0) 1 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t; split_ifs <;> norm_num
    · intro t; split_ifs <;> norm_num
    · simpa using variation_step_le (fun t : ℝ => 0 < t)
        (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  have hmask := hstep.mask (by norm_num) (by norm_num) (fun t => t ≤ s)
    (Or.inr (by intro x y hxy hy; exact hxy.trans hy))
  convert hmask using 1
  · funext t
    by_cases ht : 0 < t <;> by_cases hts : t ≤ s <;> simp [ht, hts]
  · norm_num

theorem triangularKernel_control (s : ℝ) : VariationControl (triangularKernel s) 1 2 := by
  have hstep : VariationControl (fun t : ℝ => if 0 < t then 1 else 0) 1 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t; split_ifs <;> norm_num
    · intro t; split_ifs <;> norm_num
    · simpa using variation_step_le (fun t : ℝ => 0 < t)
        (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  have hmask := hstep.mask (by norm_num) (by norm_num) (fun t => t < 1 - s)
    (Or.inr (by intro x y hxy hy; exact hxy.trans_lt hy))
  convert hmask using 1
  · funext t
    by_cases ht : 0 < t <;> by_cases hts : t < 1 - s <;>
      simp [triangularKernel, ht, hts]
  · norm_num

theorem triangularKernel_BV_bound (s : ℝ) :
    BoundedVariationOn (triangularKernel s) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |triangularKernel s t|)) +
        (eVariationOn (triangularKernel s) (Icc (0 : ℝ) 1)).toReal ≤ 3 := by
  have hc := triangularKernel_control s
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc.variation
  · have hv := ENNReal.toReal_le_of_le_ofReal (by norm_num) hc.variation
    have hh : sSup (Set.range (fun t => |triangularKernel s t|)) ≤ (1 : ℝ) := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨t, rfl⟩
      dsimp only
      rw [abs_of_nonneg (hc.nonneg t)]
      exact hc.le_height t
    linarith

theorem endpoint_triangularKernel_control {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    VariationControl (fun t => triangularKernel (Int.fract (s - t)) t) 1 2 := by
  have heq : (fun t => triangularKernel (Int.fract (s - t)) t) =
      (Ioc 0 s).indicator (fun _ => (1 : ℝ)) := by
    funext t
    exact endpoint_triangularKernel_eq_indicator hs t
  rw [heq]
  exact lower_interval_control s

theorem endpoint_triangularKernel_BV_bound {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (fun t => triangularKernel (Int.fract (s - t)) t)
        (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |triangularKernel (Int.fract (s - t)) t|)) +
        (eVariationOn (fun t => triangularKernel (Int.fract (s - t)) t)
          (Icc (0 : ℝ) 1)).toReal ≤ 3 := by
  have hc := endpoint_triangularKernel_control hs
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc.variation
  · have hv := ENNReal.toReal_le_of_le_ofReal (by norm_num) hc.variation
    have hh : sSup (Set.range (fun t => |triangularKernel (Int.fract (s - t)) t|)) ≤
        (1 : ℝ) := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨t, rfl⟩
      dsimp only
      rw [abs_of_nonneg (hc.nonneg t)]
      exact hc.le_height t
    linarith

end Invariant233.ScalarSampling

end

end OAI
