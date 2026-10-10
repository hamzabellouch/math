import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTestSymmetry
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalGradientBounds

namespace OAI

/-!
# Bounds for symmetric scalar Riesz tests

Derivative bounds control the symmetric test kernel near the origin, and Schwartz
seminorms control its far-field decay. The resulting inverse-distance majorants
establish integrability by splitting into a unit ball and its closed exterior.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set
open scoped NNReal

theorem symmetricScalarRieszTestKernel_near_bound {d : ℕ} (p : ℕ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (x h : Ambient d) :
    ‖symmetricScalarRieszTestKernel (p + 1) e g x h‖ ≤
      (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) ℝ g)) *
        inverseDistancePow p 0 h := by
  let Dg := fderivCLM ℝ (Ambient d) ℝ g
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 Dg, apply_nonneg _ _⟩
  have hL : LipschitzWith L g := by
    apply lipschitzWith_of_nnnorm_fderiv_le g.differentiable
    intro y
    have hb : ‖fderiv ℝ g y‖ ≤ (L : ℝ) := Dg.norm_le_seminorm ℝ y
    exact_mod_cast hb
  have hpoint : ‖(x + h) - (x - h)‖ ≤ 2 * ‖h‖ := by
    calc
      _ = ‖h + h‖ := by congr 1; abel
      _ ≤ ‖h‖ + ‖h‖ := norm_add_le _ _
      _ = _ := by ring
  have hd : |g (x + h) - g (x - h)| ≤ 2 * (L : ℝ) * ‖h‖ := by
    simpa only [Real.norm_eq_abs, mul_left_comm, mul_assoc] using!
      (hL.norm_sub_le (x + h) (x - h)).trans
        (mul_le_mul_of_nonneg_left hpoint L.coe_nonneg)
  have hi : |inner ℝ e h| ≤ ‖e‖ * ‖h‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e h
  by_cases hh : h = 0
  · subst h
    simp only [symmetricScalarRieszTestKernel, inner_zero_right, zero_mul, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (apply_nonneg _ _)) (inverseDistancePow_nonneg _ _ _)
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  rw [symmetricScalarRieszTestKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inverseDistancePow_nonneg _ _ _), abs_mul]
  calc
    _ ≤ inverseDistancePow (p + 1 + 1) 0 h *
        ((‖e‖ * ‖h‖) * (2 * (L : ℝ) * ‖h‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hi hd (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (inverseDistancePow_nonneg _ _ _)
    _ = _ := by
      dsimp only [L, Dg]
      simp only [inverseDistancePow, dist_zero_left, pow_succ]
      field_simp
      rfl

theorem schwartz_value_radial_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (x z h : Ambient d)
    (hh : ‖h‖ ≤ 2 * (‖z‖ + ‖x‖)) :
    ‖h‖ * ‖g z‖ ≤ 2 * (SchwartzMap.seminorm ℝ 1 0 g +
      ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g) := by
  have h0 := g.norm_le_seminorm ℝ z
  have h1 : ‖z‖ * ‖g z‖ ≤ SchwartzMap.seminorm ℝ 1 0 g := by
    simpa only [pow_one] using! g.norm_pow_mul_le_seminorm ℝ 1 z
  calc
    _ ≤ (2 * (‖z‖ + ‖x‖)) * ‖g z‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = 2 * (‖z‖ * ‖g z‖ + ‖x‖ * ‖g z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add h1 (mul_le_mul_of_nonneg_left h0 (norm_nonneg _))) (by norm_num)

theorem symmetricScalarRieszTestKernel_far_bound {d : ℕ} (m : ℕ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (x h : Ambient d) :
    ‖symmetricScalarRieszTestKernel m e g x h‖ ≤
      (4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g +
        ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g)) * inverseDistancePow (m + 1) 0 h := by
  have hp := schwartz_value_radial_bound g x (x + h) h
    (by simpa only [one_smul] using! norm_le_twice_affine_shift x h 1 (by norm_num))
  have hm := schwartz_value_radial_bound g x (x - h) h
    (by simpa only [one_smul, norm_neg, sub_eq_add_neg] using!
      norm_le_twice_affine_shift x (-h) 1 (by norm_num))
  have hi : |inner ℝ e h| ≤ ‖e‖ * ‖h‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e h
  have hd : |g (x + h) - g (x - h)| ≤ ‖g (x + h)‖ + ‖g (x - h)‖ := by
    simpa only [Real.norm_eq_abs] using! norm_sub_le (g (x + h)) (g (x - h))
  have hb : |inner ℝ e h| * |g (x + h) - g (x - h)| ≤
      4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g) := by
    calc
      _ ≤ (‖e‖ * ‖h‖) * (‖g (x + h)‖ + ‖g (x - h)‖) :=
        mul_le_mul hi hd (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖e‖ * (‖h‖ * ‖g (x + h)‖ + ‖h‖ * ‖g (x - h)‖) := by ring
      _ ≤ ‖e‖ * (2 * (SchwartzMap.seminorm ℝ 1 0 g + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g) +
          2 * (SchwartzMap.seminorm ℝ 1 0 g + ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g)) :=
        mul_le_mul_of_nonneg_left (add_le_add hp hm) (norm_nonneg _)
      _ = _ := by ring
  rw [symmetricScalarRieszTestKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inverseDistancePow_nonneg _ _ _), abs_mul]
  exact (mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)).trans_eq (mul_comm _ _)

theorem symmetricScalarRieszTestKernel_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hμ : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (x : Ambient d) :
    Integrable (symmetricScalarRieszTestKernel (p + 1) e g x) μ := by
  have hc : Continuous (fun h : Ambient d => inner ℝ e h * (g (x + h) - g (x - h))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (symmetricScalarRieszTestKernel (p + 1) e g x) μ :=
    (inverseDistancePow_measurable (p + 1 + 1) (0 : Ambient d)).aestronglyMeasurable.mul
      hc.aestronglyMeasurable
  have hn : IntegrableOn (symmetricScalarRieszTestKernel (p + 1) e g x) (closedBall 0 1) μ := by
    have hi := (inverseDistancePow_near_integrable_and_bound p C μ hμ 0 1 (by norm_num)).1
    apply (hi.const_mul (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0
      (fderivCLM ℝ (Ambient d) ℝ g))).mono' hmeas.restrict
    exact Eventually.of_forall (symmetricScalarRieszTestKernel_near_bound p e g x)
  have hf : IntegrableOn (symmetricScalarRieszTestKernel (p + 1) e g x) (closedExterior 0 1) μ := by
    have hi := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) C μ hμ 0 1
      (by norm_num)).1
    apply (hi.const_mul (4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g +
      ‖x‖ * SchwartzMap.seminorm ℝ 0 0 g))).mono' hmeas.restrict
    exact Eventually.of_forall (symmetricScalarRieszTestKernel_far_bound (p + 1) e g x)
  have hs : closedBall (0 : Ambient d) 1 ∪ closedExterior 0 1 = univ := by
    ext h
    simp only [mem_union, mem_closedBall, dist_zero_right, closedExterior, mem_ofPred_eq,
      dist_zero_left, mem_univ, iff_true]
    exact le_total ‖h‖ 1
  have hi := hn.union hf
  rw [hs] at hi
  exact integrableOn_univ.mp hi

end

end RieszRectifiability

end OAI
