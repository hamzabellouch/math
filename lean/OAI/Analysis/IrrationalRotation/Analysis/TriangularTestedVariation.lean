import OAI.Analysis.IrrationalRotation.Analysis.TriangularEndpointKernel

namespace OAI

noncomputable section
open Set

namespace Invariant233.ScalarSampling

theorem VariationControl.mul_interval_indicator {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (g : ℝ → ℝ) (hg : Monotone g ∨ Antitone g) (a b : ℝ) :
    VariationControl (fun t => f t * (Ico a b).indicator (fun _ => 1) (g t))
      C (V + 2 * C) := by
  have ha : (∀ x y, x ≤ y → a ≤ g x → a ≤ g y) ∨
      (∀ x y, x ≤ y → a ≤ g y → a ≤ g x) := by
    rcases hg with hg | hg
    · exact Or.inl (fun _ _ hxy hx => hx.trans (hg hxy))
    · exact Or.inr (fun _ _ hxy hy => hy.trans (hg hxy))
  have hb : (∀ x y, x ≤ y → g x < b → g y < b) ∨
      (∀ x y, x ≤ y → g y < b → g x < b) := by
    rcases hg with hg | hg
    · exact Or.inr (fun _ _ hxy hy => (hg hxy).trans_lt hy)
    · exact Or.inl (fun _ _ hxy hx => (hg hxy).trans_lt hx)
  have h1 := hf.mask hC hV (fun t => a ≤ g t) ha
  have h2 := h1.mask hC (add_nonneg hV hC) (fun t => g t < b) hb
  convert h2 using 1
  · funext t
    by_cases hat : a ≤ g t <;> by_cases hbt : g t < b <;> simp [hat, hbt]
  · ring

theorem VariationControl.fixed_indicator_mul {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (E : Set ℝ) (s : ℝ) :
    VariationControl (fun t => E.indicator (fun _ => 1) s * f t) C V := by
  by_cases hs : s ∈ E
  · simpa [hs] using hf
  · simp only [Set.indicator_of_notMem hs, zero_mul]
    refine ⟨fun _ => le_rfl, fun _ => hC, ?_⟩
    have hzero : eVariationOn (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) 1) = 0 := by
      apply (eVariationOn.eq_zero_iff _).2
      intro x hx y hy
      exact edist_self _
    rw [hzero]
    exact bot_le

theorem VariationControl.boundedVariation_sup_add_le {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hV : 0 ≤ V) :
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) +
        (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ C + V := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf.variation
  · have hv := ENNReal.toReal_le_of_le_ofReal hV hf.variation
    have hh : sSup (Set.range (fun t => |f t|)) ≤ C := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨t, rfl⟩
      dsimp only
      rw [abs_of_nonneg (hf.nonneg t)]
      exact hf.le_height t
    exact add_le_add hh hv

theorem triangularKernel_mul_test_unwrap {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (F : ℝ → ℝ) (t : ℝ) :
    triangularKernel s t * F (Int.fract (s + t)) = triangularKernel s t * F (s + t) := by
  by_cases ht : t ∈ Ioo 0 (1 - s)
  · have hfract : Int.fract (s + t) = s + t :=
      Int.fract_eq_self.mpr ⟨by linarith [hs.1, ht.1], by linarith [ht.2]⟩
    rw [hfract]
  · simp [triangularKernel, ht]

theorem endpoint_triangularKernel_mul_test_unwrap {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (F : ℝ → ℝ) (t : ℝ) :
    triangularKernel (Int.fract (s - t)) t * F (Int.fract (s - t)) =
      triangularKernel (Int.fract (s - t)) t * F (s - t) := by
  by_cases ht : t ∈ Ioc 0 s
  · have hfract : Int.fract (s - t) = s - t :=
      Int.fract_eq_self.mpr ⟨by linarith [ht.2], by linarith [hs.2, ht.1]⟩
    rw [hfract]
  · rw [endpoint_triangularKernel_eq_indicator hs]
    simp [ht]

theorem tested_triangularKernel_control {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (a b c d : ℝ) :
    VariationControl (fun t => triangularKernel s t *
      (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s + t))) 1 4 := by
  have hc := (triangularKernel_control s).mul_interval_indicator
    (by norm_num) (by norm_num) (fun t => s + t)
    (Or.inl (by intro x y hxy; dsimp only; linarith)) c d
  have hfixed := hc.fixed_indicator_mul (by norm_num) (Ico a b) s
  have heq : (fun t => triangularKernel s t * (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s + t))) =
      fun t => (Ico a b).indicator (fun _ => 1) s *
        (triangularKernel s t * (Ico c d).indicator (fun _ => 1) (s + t)) := by
    funext t
    calc
      _ = (Ico a b).indicator (fun _ => 1) s *
          (triangularKernel s t *
            (Ico c d).indicator (fun _ => 1) (Int.fract (s + t))) := by ring
      _ = _ := by rw [triangularKernel_mul_test_unwrap hs]
  rw [heq]
  convert hfixed using 1
  norm_num

theorem tested_endpoint_triangularKernel_control {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (a b c d : ℝ) :
    VariationControl (fun t => triangularKernel (Int.fract (s - t)) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s - t)) *
      (Ico c d).indicator (fun _ => 1) s) 1 4 := by
  have hc := (endpoint_triangularKernel_control hs).mul_interval_indicator
    (by norm_num) (by norm_num) (fun t => s - t)
    (Or.inr (by intro x y hxy; exact sub_le_sub_left hxy s)) a b
  have hfixed := hc.fixed_indicator_mul (by norm_num) (Ico c d) s
  have heq : (fun t => triangularKernel (Int.fract (s - t)) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s - t)) *
      (Ico c d).indicator (fun _ => 1) s) =
      fun t => (Ico c d).indicator (fun _ => 1) s *
        (triangularKernel (Int.fract (s - t)) t *
          (Ico a b).indicator (fun _ => 1) (s - t)) := by
    funext t
    calc
      _ = (Ico c d).indicator (fun _ => 1) s *
          (triangularKernel (Int.fract (s - t)) t *
            (Ico a b).indicator (fun _ => 1) (Int.fract (s - t))) := by ring
      _ = _ := by rw [endpoint_triangularKernel_mul_test_unwrap hs]
  rw [heq]
  convert hfixed using 1
  norm_num

theorem tested_triangularKernel_BV_bound {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (a b c d : ℝ) :
    let f := fun t => triangularKernel s t * (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s + t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ 5 := by
  simpa only [show (1 : ℝ) + 4 = 5 by norm_num] using (tested_triangularKernel_control hs a b c d).boundedVariation_sup_add_le
    (by norm_num)

theorem tested_endpoint_triangularKernel_BV_bound {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (a b c d : ℝ) :
    let f := fun t => triangularKernel (Int.fract (s - t)) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s - t)) *
      (Ico c d).indicator (fun _ => 1) s
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ 5 := by
  simpa only [show (1 : ℝ) + 4 = 5 by norm_num] using (tested_endpoint_triangularKernel_control hs a b c d).boundedVariation_sup_add_le
    (by norm_num)

end Invariant233.ScalarSampling

end

end OAI
