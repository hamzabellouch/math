import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalTestDilation

namespace OAI

/-!
# Bounds for dilated fractional gradients

Lipschitz control of the derivative bounds symmetric dilated differences near the
origin. Radial Schwartz decay controls the far region, providing the two estimates
needed for fractional-gradient integrability and dilation arguments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lipschitz_fderiv_dilated_difference_bound {d : ℕ}
    (g : Ambient d → F) (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ g))
    (x h : Ambient d) (t : ℝ) (ht : |t| ≤ 2) :
    ‖fderiv ℝ g (x + t • h) h - fderiv ℝ g (x - t • h) h‖ ≤
      4 * (L : ℝ) * ‖h‖ ^ 2 := by
  have hpoint : ‖(x + t • h) - (x - t • h)‖ ≤ 4 * ‖h‖ := by
    calc
      _ = ‖t • h + t • h‖ := by congr 1; abel
      _ ≤ ‖t • h‖ + ‖t • h‖ := norm_add_le _ _
      _ = 2 * |t| * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg h)]
  calc
    _ = ‖(fderiv ℝ g (x + t • h) - fderiv ℝ g (x - t • h)) h‖ := by
      rw [sub_apply]
    _ ≤ ‖fderiv ℝ g (x + t • h) - fderiv ℝ g (x - t • h)‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((L : ℝ) * (4 * ‖h‖)) * ‖h‖ :=
      mul_le_mul_of_nonneg_right ((hL.norm_sub_le _ _).trans
        (mul_le_mul_of_nonneg_left hpoint L.coe_nonneg)) (norm_nonneg _)
    _ = _ := by ring

theorem schwartz_dilated_fractional_gradient_near_bound {d : ℕ} (p : ℕ)
    (g : 𝓢(Ambient d, F)) (x h : Ambient d) (t : ℝ) (ht : |t| ≤ 2) :
    ‖dilatedFractionalGradientKernel (p + 1) g x t h‖ ≤
      (4 * SchwartzMap.seminorm ℝ 0 0
        (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g))) *
          inverseDistancePow p 0 h := by
  let Dg := fderivCLM ℝ (Ambient d) F g
  let DDg := fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) Dg
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 DDg, apply_nonneg _ _⟩
  have hL : LipschitzWith L Dg := by
    apply lipschitzWith_of_nnnorm_fderiv_le Dg.differentiable
    intro y
    have hb : ‖fderiv ℝ Dg y‖ ≤ (L : ℝ) := DDg.norm_le_seminorm ℝ y
    exact_mod_cast hb
  have hb := lipschitz_fderiv_dilated_difference_bound g L hL x h t ht
  rw [dilatedFractionalGradientKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [map_zero, sub_zero, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _))
      (inverseDistancePow_nonneg _ _ _)
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  calc
    _ ≤ inverseDistancePow (p + 1 + 1) 0 h * (4 * (L : ℝ) * ‖h‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
    _ = _ := by
      dsimp only [L, DDg, Dg]
      simp only [inverseDistancePow, dist_zero_left, pow_succ]
      field_simp
      rfl

theorem norm_le_twice_affine_shift {d : ℕ} (x h : Ambient d) (t : ℝ) (ht : 1 / 2 ≤ t) :
    ‖h‖ ≤ 2 * (‖x + t • h‖ + ‖x‖) := by
  have hpos : 0 < t := by linarith
  have hn := norm_sub_le (x + t • h) x
  have heq : x + t • h - x = t • h := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hn
  nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg h)]

theorem schwartz_operator_apply_radial_bound {d : ℕ}
    (G : 𝓢(Ambient d, Ambient d →L[ℝ] F)) (x z h : Ambient d)
    (hh : ‖h‖ ≤ 2 * (‖z‖ + ‖x‖)) :
    ‖G z h‖ ≤ 2 * (SchwartzMap.seminorm ℝ 1 0 G + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 G) := by
  have h0 := G.norm_le_seminorm ℝ z
  have h1 : ‖z‖ * ‖G z‖ ≤ SchwartzMap.seminorm ℝ 1 0 G := by
    simpa only [pow_one] using! G.norm_pow_mul_le_seminorm ℝ 1 z
  calc
    _ ≤ ‖G z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖G z‖ * (2 * (‖z‖ + ‖x‖)) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = 2 * (‖z‖ * ‖G z‖ + ‖x‖ * ‖G z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add h1 (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))) (by norm_num)

theorem schwartz_dilated_fractional_gradient_far_bound {d : ℕ} (m : ℕ)
    (g : 𝓢(Ambient d, F)) (x h : Ambient d) (t : ℝ) (ht : 1 / 2 ≤ t) :
    ‖dilatedFractionalGradientKernel m g x t h‖ ≤
      (4 * (SchwartzMap.seminorm ℝ 1 0 (fderivCLM ℝ (Ambient d) F g) +
        ‖x‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) F g))) *
          inverseDistancePow (m + 1) 0 h := by
  let Dg := fderivCLM ℝ (Ambient d) F g
  have hp := schwartz_operator_apply_radial_bound Dg x (x + t • h) h
    (norm_le_twice_affine_shift x h t ht)
  have hminus : ‖h‖ ≤ 2 * (‖x - t • h‖ + ‖x‖) := by
    simpa only [norm_neg, smul_neg, sub_eq_add_neg] using! norm_le_twice_affine_shift x (-h) t ht
  have hm := schwartz_operator_apply_radial_bound Dg x (x - t • h) h hminus
  rw [dilatedFractionalGradientKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  calc
    _ ≤ inverseDistancePow (m + 1) 0 h * (‖Dg (x + t • h) h‖ + ‖Dg (x - t • h) h‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inverseDistancePow_nonneg _ _ _)
    _ ≤ inverseDistancePow (m + 1) 0 h *
        (2 * (SchwartzMap.seminorm ℝ 1 0 Dg + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 Dg) +
         2 * (SchwartzMap.seminorm ℝ 1 0 Dg + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 Dg)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hm) (inverseDistancePow_nonneg _ _ _)
    _ = _ := by dsimp only [Dg]; ring

end

end RieszRectifiability

end OAI
