import OAI.Analysis.IrrationalRotation.Analysis.TriangularTestedVariation

namespace OAI

noncomputable section
open Set

namespace Invariant233.ScalarSampling

lemma circleKernel_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (circleKernel h α s) (h * α)⁻¹ (2 * (h * α)⁻¹) := by
  refine ⟨?_, ?_, circleKernel_variation_le hh hhone hα s⟩
  · intro t
    exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  · intro t
    exact rawKernel_le_height hh hα _ _

lemma circleEndpoint_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (fun t => circleKernel h α (s-t) t)
      (h * α)⁻¹ (10 * (h * α)⁻¹) := by
  refine ⟨?_, ?_, circleEndpoint_variation_le hh hhone hα s⟩
  · intro t
    exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg (s-t), (Int.fract_lt_one (s-t)).le⟩
  · intro t
    exact rawKernel_le_height hh hα _ _

lemma rawKernel_support_of_ne_zero {h α s t : ℝ}
    (hk : rawKernel h α s t ≠ 0) :
    α ≤ delta s ∧ 0 < t ∧ t < h * delta s := by
  by_cases hc : α ≤ delta s
  · refine ⟨hc, ?_⟩
    by_contra ht
    apply hk
    simp only [rawKernel, ite_eq_left hc]
    exact Set.indicator_of_notMem (s := Ioo 0 (h * delta s)) (a := t) ht
      (fun _ : ℝ => (h * delta s)⁻¹)
  · exact False.elim (hk (by simp [rawKernel, hc]))

lemma circleKernel_target_no_wrap {h α s t : ℝ} (hhone : h ≤ 1)
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : circleKernel h α s t ≠ 0) : Int.fract (s+t) = s+t := by
  have hr : rawKernel h α s t ≠ 0 := by
    simpa only [circleKernel_eq_raw_on_unit hhone s ht,
      Int.fract_eq_self.mpr hs] using hk
  have hp := rawKernel_support_of_ne_zero hr
  have hd : 0 ≤ delta s := delta_nonneg ⟨hs.1, hs.2.le⟩
  have hwidth : h * delta s ≤ 1-s := by
    calc
      h * delta s ≤ delta s := by nlinarith
      _ ≤ 1-s := min_le_right _ _
  exact Int.fract_eq_self.mpr ⟨by linarith [ht.1, hs.1], by linarith [hp.2.2]⟩

lemma circleEndpoint_source_no_wrap {h α s t : ℝ} (hh : 0 ≤ h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : circleKernel h α (s-t) t ≠ 0) : Int.fract (s-t) = s-t := by
  have hr : rawKernel h α (s-t) t ≠ 0 := by
    rwa [endpoint_no_wrap_on_unit hh hhone hα hs ht] at hk
  have hp := (rawKernel_support_of_ne_zero hr).1
  have hleft : delta (s-t) ≤ s-t := min_le_left _ _
  have hright : delta (s-t) ≤ 1-(s-t) := min_le_right _ _
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

private lemma mul_two_tests_bounds {x C : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C)
    (hC : 0 ≤ C) (E F : Set ℝ) (s t : ℝ) :
    0 ≤ x * E.indicator (fun _ => 1) s * F.indicator (fun _ => 1) t ∧
      x * E.indicator (fun _ => 1) s * F.indicator (fun _ => 1) t ≤ C := by
  by_cases hs : s ∈ E <;> by_cases ht : t ∈ F <;> simp [hs, ht, hx, hxC, hC]

theorem tested_circleKernel_control {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    VariationControl (fun t => circleKernel h α s t *
      (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s+t)))
      (h * α)⁻¹ (4 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := circleKernel_control hh hhone hα s
  have hc := hb.mul_interval_indicator hC (by positivity) (fun t => s+t)
    (Or.inl (by intro x y hxy; dsimp only; linarith)) c d
  have hfixed : VariationControl (fun t => (Ico a b).indicator (fun _ => 1) s *
      (circleKernel h α s t * (Ico c d).indicator (fun _ => 1) (s+t)))
      (h * α)⁻¹ (4 * (h * α)⁻¹) := by
    convert hc.fixed_indicator_mul hC (Ico a b) s using 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) s (Int.fract (s+t))).1
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) s (Int.fract (s+t))).2
  · have heq : EqOn (fun t => circleKernel h α s t *
        (Ico a b).indicator (fun _ => 1) s *
        (Ico c d).indicator (fun _ => 1) (Int.fract (s+t)))
        (fun t => (Ico a b).indicator (fun _ => 1) s *
          (circleKernel h α s t * (Ico c d).indicator (fun _ => 1) (s+t)))
        (Icc (0 : ℝ) 1) := by
      intro t ht
      dsimp only
      by_cases hk : circleKernel h α s t = 0
      · simp [hk]
      · rw [circleKernel_target_no_wrap hhone hs ht hk]
        ring
    rw [eVariationOn.congr heq]
    exact hfixed.variation

theorem tested_circleEndpoint_control {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    VariationControl (fun t => circleKernel h α (s-t) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
      (Ico c d).indicator (fun _ => 1) s)
      (h * α)⁻¹ (12 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := circleEndpoint_control hh hhone hα s
  have hc := hb.mul_interval_indicator hC (by positivity) (fun t => s-t)
    (Or.inr (by intro x y hxy; exact sub_le_sub_left hxy s)) a b
  have hfixed : VariationControl (fun t => (Ico c d).indicator (fun _ => 1) s *
      (circleKernel h α (s-t) t * (Ico a b).indicator (fun _ => 1) (s-t)))
      (h * α)⁻¹ (12 * (h * α)⁻¹) := by
    convert hc.fixed_indicator_mul hC (Ico c d) s using 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) (Int.fract (s-t)) s).1
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) (Int.fract (s-t)) s).2
  · have heq : EqOn (fun t => circleKernel h α (s-t) t *
        (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
        (Ico c d).indicator (fun _ => 1) s)
        (fun t => (Ico c d).indicator (fun _ => 1) s *
          (circleKernel h α (s-t) t * (Ico a b).indicator (fun _ => 1) (s-t)))
        (Icc (0 : ℝ) 1) := by
      intro t ht
      dsimp only
      by_cases hk : circleKernel h α (s-t) t = 0
      · simp [hk]
      · rw [circleEndpoint_source_no_wrap hh.le hhone hα hs ht hk]
        ring
    rw [eVariationOn.congr heq]
    exact hfixed.variation

theorem tested_circleKernel_BV_bound {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => circleKernel h α s t * (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s+t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        5 * (h * α)⁻¹ := by
  simpa only [show (h * α)⁻¹ + 4 * (h * α)⁻¹ = 5 * (h * α)⁻¹ by ring] using
    (tested_circleKernel_control hh hhone hα hs a b c d).boundedVariation_sup_add_le
      (by positivity)

theorem tested_circleEndpoint_BV_bound {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => circleKernel h α (s-t) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) * (Ico c d).indicator (fun _ => 1) s
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        13 * (h * α)⁻¹ := by
  simpa only [show (h * α)⁻¹ + 12 * (h * α)⁻¹ = 13 * (h * α)⁻¹ by ring] using
    (tested_circleEndpoint_control hh hhone hα hs a b c d).boundedVariation_sup_add_le
      (by positivity)

theorem tested_manuscriptKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => manuscriptKernel m s t * (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s+t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        5 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, manuscript_reciprocal_height hm] using
    tested_circleKernel_BV_bound hh hhone hα hs a b c d

theorem tested_manuscriptEndpointKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => manuscriptEndpointKernel m s t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) * (Ico c d).indicator (fun _ => 1) s
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        13 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, manuscript_reciprocal_height hm] using
    tested_circleEndpoint_BV_bound hh hhone hα hs a b c d

theorem tested_manuscript_oriented_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (endpoint : Bool) (a b c d : ℝ) :
    let f := fun t => if endpoint then
      manuscriptEndpointKernel m s t * (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
        (Ico c d).indicator (fun _ => 1) s
      else manuscriptKernel m s t * (Ico a b).indicator (fun _ => 1) s *
        (Ico c d).indicator (fun _ => 1) (Int.fract (s+t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        13 * (m : ℝ)^10 := by
  have hp : (m : ℝ) ^ (13 / 5 : ℝ) ≤ (m : ℝ)^10 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
      (by norm_num)
  cases endpoint
  · simp only [Bool.false_eq_true, ite_false]
    have hb := tested_manuscriptKernel_BV_bound hm hs a b c d
    refine ⟨hb.1, hb.2.trans ?_⟩
    calc
      5 * (m : ℝ) ^ (13 / 5 : ℝ) ≤ 13 * (m : ℝ) ^ (13 / 5 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (by norm_num)
        positivity
      _ ≤ 13 * (m : ℝ)^10 := mul_le_mul_of_nonneg_left hp (by norm_num)
  · simp only [ite_true]
    have hb := tested_manuscriptEndpointKernel_BV_bound hm hs a b c d
    exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left hp (by norm_num))⟩

end Invariant233.ScalarSampling

end

end OAI
