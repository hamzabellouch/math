import OAI.MeasureTheory.Falconer.Shells.OriginalShellIntegral
import OAI.MeasureTheory.Falconer.Angular.FiniteAngularSquare

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem dyadic_shell_smooth_domination (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hb : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hCbound : ∀ r, ‖F r‖ ≤ C) :
    (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
      (2:ℝ)^v * ∫ r, ‖F r‖^2 ∂sourceAngularShellMeasure v Ψ := by
  have hR : 0 < (2:ℝ)^v := by positivity
  have hzero : ∀ x ≤ 0, Ψ x = 0 := by
    intro x hx
    by_contra hn
    have := (hs x hn).1
    linarith
  rw [sourceAngularShellMeasure_integral v hΨ hpos hzero,smul_eq_mul,
    ← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul]
  have hi : Integrable (fun r => Ψ (r/(2:ℝ)^v)*‖F r‖^2) := by
    exact bounded_shell_integrable hΨ hs hW
      (fun x => by rw [abs_of_nonneg (hpos x)]; exact hb x) hR _
      (hF.norm.pow_const 2).aestronglyMeasurable (sq_nonneg C) (fun r => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCbound r) 2)
  have hfi : IntegrableOn (fun r => ‖F r‖^2)
      (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) :=
    integrable_norm_square_bounded _ F hF hC (Filter.Eventually.of_forall hCbound)
  rw [← integral_indicator measurableSet_Icc]
  apply integral_mono (hfi.integrable_indicator measurableSet_Icc) hi
  intro r
  by_cases hr : r ∈ Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))
  · rw [indicator_of_mem hr]
    have he₁ : (2:ℝ)^(v-1) = (2:ℝ)^v/2 := by
      rw [Real.rpow_sub (by norm_num)]; norm_num
    have he₂ : (2:ℝ)^(v+1) = 2*(2:ℝ)^v := by
      rw [Real.rpow_add (by norm_num)]; norm_num; ring
    have hh : r/(2:ℝ)^v ∈ Icc (1/2:ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ hR).mpr
        rw [he₁] at hr
        linarith [hr.1]
      · apply (div_le_iff₀ hR).mpr
        simpa only [he₂] using hr.2
    exact le_mul_of_one_le_left (sq_nonneg _) (hone _ hh)
  · rw [indicator_of_notMem hr]
    exact mul_nonneg (hpos _) (sq_nonneg _)

theorem dyadic_shell_le_radial_energy (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hb : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hCbound : ∀ r, ‖F r‖ ≤ C) {H : ℝ}
    (hH : sourceRadialSquareEnergy a v Ψ F ≤ H) :
    (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
      ((2:ℝ)^v/(2:ℝ)^(2*(v-a)))*H := by
  apply (dyadic_shell_smooth_domination v Ψ hΨ hpos hs hW hb hone F hF hC hCbound).trans
  have hh := (le_div_iff₀ (show 0 < (2:ℝ)^(2*(v-a)) by positivity)).mpr
    (show (∫ r, ‖F r‖^2 ∂sourceAngularShellMeasure v Ψ)*(2:ℝ)^(2*(v-a)) ≤ H by
      simpa only [sourceRadialSquareEnergy,mul_comm] using hH)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

end PlanarFalconer

end OAI
