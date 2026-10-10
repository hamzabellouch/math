import OAI.Analysis.IrrationalRotation.Analysis.TestedTriangularMoments

namespace OAI

noncomputable section
open Set
attribute [local instance] Classical.propDecidable

namespace Invariant233.ScalarSampling.TestedTriangular

theorem firstKernel_interval_eq (E : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    firstKernel E (Ico a b) s t =
      if s ∈ E then
        if a ≤ s + t then if s + t < b then triangularKernel s t else 0 else 0
      else 0 := by
  by_cases ht : t ∈ Ioo 0 (1 - s)
  · have hfract : Int.fract (s + t) = s + t :=
      Int.fract_eq_self.mpr ⟨by linarith [hs.1, ht.1], by linarith [ht.2]⟩
    by_cases hE : s ∈ E <;> by_cases ha : a ≤ s + t <;> by_cases hb : s + t < b <;>
      simp [firstKernel, triangularKernel, ht, hfract, hE, ha, hb]
  · simp [firstKernel, triangularKernel, ht]

theorem secondKernel_interval_eq (F : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    secondKernel (Ico a b) F s t =
      if s ∈ F then
        if a ≤ s - t then
          if s - t < b then triangularKernel (Int.fract (s - t)) t else 0
        else 0
      else 0 := by
  by_cases ht : t ∈ Ioc 0 s
  · have hfract : Int.fract (s - t) = s - t :=
      Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht.2, by linarith [hs.2, ht.1]⟩
    by_cases hF : s ∈ F <;> by_cases ha : a ≤ s - t <;> by_cases hb : s - t < b <;>
      simp [secondKernel, hfract, hF, ha, hb]
  · have hzero : triangularKernel (Int.fract (s - t)) t = 0 := by
      rw [endpoint_triangularKernel_eq_indicator hs t]
      exact indicator_of_notMem ht _
    simp [secondKernel, hzero]

private theorem zero_control : VariationControl (fun _ : ℝ => 0) 1 4 := by
  refine ⟨fun _ => le_rfl, fun _ => zero_le_one, ?_⟩
  have hz := monotone_variation_le_height
    (f := fun _ : ℝ => 0) (C := 0) (by intro x hx y hy hxy; rfl)
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  exact hz.trans (by norm_num)

theorem firstKernel_interval_control (E : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    VariationControl (firstKernel E (Ico a b) s) 1 4 := by
  have h1 := (triangularKernel_control s).mask (by norm_num) (by norm_num)
    (fun t => s + t < b)
    (Or.inr (by intro x y hxy hy; linarith))
  have h2 := h1.mask (by norm_num) (by norm_num) (fun t => a ≤ s + t)
    (Or.inl (by intro x y hxy hx; linarith))
  by_cases hE : s ∈ E
  · convert h2 using 1
    · funext t
      simp only [firstKernel_interval_eq E a b hs t, ite_eq_left hE]
    · norm_num
  · have heq : firstKernel E (Ico a b) s = fun _ => 0 := by
      funext t
      simp [firstKernel_interval_eq E a b hs t, hE]
    rw [heq]
    exact zero_control

theorem secondKernel_interval_control (F : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    VariationControl (secondKernel (Ico a b) F s) 1 4 := by
  have h1 := (endpoint_triangularKernel_control hs).mask (by norm_num) (by norm_num)
    (fun t => s - t < b)
    (Or.inl (by intro x y hxy hx; linarith))
  have h2 := h1.mask (by norm_num) (by norm_num) (fun t => a ≤ s - t)
    (Or.inr (by intro x y hxy hy; linarith))
  by_cases hF : s ∈ F
  · convert h2 using 1
    · funext t
      simp only [secondKernel_interval_eq F a b hs t, ite_eq_left hF]
    · norm_num
  · have heq : secondKernel (Ico a b) F s = fun _ => 0 := by
      funext t
      simp [secondKernel_interval_eq F a b hs t, hF]
    rw [heq]
    exact zero_control

private theorem BV_bound_of_control {f : ℝ → ℝ} (hf : VariationControl f 1 4) :
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) +
        (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ 5 := by
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf.variation, ?_⟩
  have hv := ENNReal.toReal_le_of_le_ofReal (by norm_num) hf.variation
  have hh : sSup (Set.range (fun t => |f t|)) ≤ (1 : ℝ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    dsimp only
    rw [abs_of_nonneg (hf.nonneg t)]
    exact hf.le_height t
  linarith

theorem firstKernel_interval_BV_bound (E : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (firstKernel E (Ico a b) s) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |firstKernel E (Ico a b) s t|)) +
        (eVariationOn (firstKernel E (Ico a b) s) (Icc (0 : ℝ) 1)).toReal ≤ 5 :=
  BV_bound_of_control (firstKernel_interval_control E a b hs)

theorem secondKernel_interval_BV_bound (F : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (secondKernel (Ico a b) F s) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |secondKernel (Ico a b) F s t|)) +
        (eVariationOn (secondKernel (Ico a b) F s) (Icc (0 : ℝ) 1)).toReal ≤ 5 :=
  BV_bound_of_control (secondKernel_interval_control F a b hs)

end Invariant233.ScalarSampling.TestedTriangular

end

end OAI
