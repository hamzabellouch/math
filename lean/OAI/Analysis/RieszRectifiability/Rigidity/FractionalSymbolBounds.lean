import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel

namespace OAI

/-!
# Bounds for the fractional symbol

The cosine difference defining the fractional symbol is nonnegative and has quadratic
cancellation near the origin. Combining this local bound with inverse-power decay at
infinity gives integrability under upper growth bounds, in particular for volume.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

def fractionalSymbolKernel {d : ℕ} (m : ℕ) (ξ h : Ambient d) : ℝ :=
  inverseDistancePow (m + 1) 0 h * (1 - Real.cos (2 * Real.pi * inner ℝ ξ h))

def fractionalSymbol (p : ℕ) (ξ : Ambient (p + 1)) : ℝ :=
  ∫ h, fractionalSymbolKernel (p + 1) ξ h

theorem fractionalSymbolKernel_nonneg {d : ℕ} (m : ℕ) (ξ h : Ambient d) :
    0 ≤ fractionalSymbolKernel m ξ h :=
  mul_nonneg (inverseDistancePow_nonneg _ _ _) (sub_nonneg.mpr (Real.cos_le_one _))

theorem fractionalSymbolKernel_measurable {d : ℕ} (m : ℕ) (ξ : Ambient d) :
    Measurable (fractionalSymbolKernel m ξ) := by
  unfold fractionalSymbolKernel inverseDistancePow
  fun_prop

theorem one_sub_cos_inner_quadratic {d : ℕ} (ξ h : Ambient d) :
    1 - Real.cos (2 * Real.pi * inner ℝ ξ h) ≤
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖h‖ ^ 2 := by
  have hc : 1 - Real.cos (2 * Real.pi * inner ℝ ξ h) ≤
      (2 * Real.pi * inner ℝ ξ h) ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * inner ℝ ξ h),
      sq_nonneg (2 * Real.pi * inner ℝ ξ h)]
  have hi : (inner ℝ ξ h) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖h‖ ^ 2 := by
    simpa only [sq_abs, mul_pow] using!
      (sq_le_sq₀ (abs_nonneg (inner ℝ ξ h))
        (mul_nonneg (norm_nonneg ξ) (norm_nonneg h))).mpr (abs_real_inner_le_norm ξ h)
  calc
    _ ≤ (2 * Real.pi * inner ℝ ξ h) ^ 2 := hc
    _ = (2 * Real.pi) ^ 2 * (inner ℝ ξ h) ^ 2 := mul_pow _ _ _
    _ ≤ (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖h‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (sq_nonneg _)
    _ = _ := by ring

theorem fractionalSymbolKernel_near_bound {d : ℕ} (p : ℕ) (ξ h : Ambient d) :
    ‖fractionalSymbolKernel (p + 1) ξ h‖ ≤
      ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) * inverseDistancePow p 0 h := by
  rw [Real.norm_of_nonneg (fractionalSymbolKernel_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [fractionalSymbolKernel, inner_zero_right, mul_zero, Real.cos_zero, sub_self]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (inverseDistancePow_nonneg _ _ _)
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h *
          ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (one_sub_cos_inner_quadratic ξ h) (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSymbolKernel_far_bound {d : ℕ} (m : ℕ) (ξ h : Ambient d) :
    ‖fractionalSymbolKernel m ξ h‖ ≤ 2 * inverseDistancePow (m + 1) 0 h := by
  rw [Real.norm_of_nonneg (fractionalSymbolKernel_nonneg _ _ _)]
  have hc : 1 - Real.cos (2 * Real.pi * inner ℝ ξ h) ≤ 2 := by
    linarith [Real.neg_one_le_cos (2 * Real.pi * inner ℝ ξ h)]
  exact (mul_le_mul_of_nonneg_left hc (inverseDistancePow_nonneg _ _ _)).trans_eq (mul_comm _ _)

theorem fractionalSymbolKernel_integrable_of_growth {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ) (ξ : Ambient d) :
    Integrable (fractionalSymbolKernel (p + 1) ξ) μ := by
  have hm : AEStronglyMeasurable (fractionalSymbolKernel (p + 1) ξ) μ :=
    (fractionalSymbolKernel_measurable (p + 1) ξ).aestronglyMeasurable
  have hnear : IntegrableOn (fractionalSymbolKernel (p + 1) ξ) (closedBall 0 1) μ := by
    have hi := (inverseDistancePow_near_integrable_and_bound p C μ hg 0 1 zero_lt_one).1
    exact (hi.const_mul ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2)).mono' hm.restrict
      (Eventually.of_forall (fractionalSymbolKernel_near_bound p ξ))
  have hfar : IntegrableOn (fractionalSymbolKernel (p + 1) ξ) (closedExterior 0 1) μ := by
    have hi := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) C μ hg 0 1 zero_lt_one).1
    exact (hi.const_mul 2).mono' hm.restrict (Eventually.of_forall (fractionalSymbolKernel_far_bound (p + 1) ξ))
  have hs : closedBall (0 : Ambient d) 1 ∪ closedExterior 0 1 = univ := by
    ext h
    simp only [mem_union, mem_closedBall, dist_zero_right, closedExterior, mem_ofPred_eq,
      dist_zero_left, mem_univ, iff_true]
    exact le_total ‖h‖ 1
  have hi := hnear.union hfar
  rw [hs] at hi
  exact integrableOn_univ.mp hi

theorem fractionalSymbolKernel_integrable (p : ℕ) (ξ : Ambient (p + 1)) :
    Integrable (fractionalSymbolKernel (p + 1) ξ) volume :=
  fractionalSymbolKernel_integrable_of_growth p _ volume (volume_global_upper_growth (p + 1)) ξ

theorem fractionalSymbol_nonneg (p : ℕ) (ξ : Ambient (p + 1)) : 0 ≤ fractionalSymbol p ξ :=
  integral_nonneg (fractionalSymbolKernel_nonneg (p + 1) ξ)

theorem fractionalSymbol_zero (p : ℕ) : fractionalSymbol p 0 = 0 := by
  simp [fractionalSymbol, fractionalSymbolKernel]

end

end RieszRectifiability

end OAI
