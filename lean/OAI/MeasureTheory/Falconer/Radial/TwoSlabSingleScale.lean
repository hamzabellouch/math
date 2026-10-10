import OAI.MeasureTheory.Falconer.Geometry.OrthonormalRectangle
import OAI.MeasureTheory.Falconer.Geometry.NormalSeparation

namespace OAI

/-! # Single-scale mass of two transverse thick hyperplanes

Only the stated concentration bound at radius r is used. The long transverse
side is covered by O(1/τ) radius-r codimension-two neighborhoods.
-/
namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem two_slab_single_scale_bound {d : ℕ} (μ : Measure (Space d))
    (u v : Space d) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a b : ℝ)
    {r τ C α : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hsep : τ ≤ normalDistance u v)
    (hplane : ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 →
      ∀ p, μ (affineSubspaceNeighborhood V p r) ≤ ENNReal.ofReal (C*r^α)) :
    μ {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ≤
      ENNReal.ofReal (252*C*r^α/τ) := by
  let w := perpendicularPart u v
  have ht : τ ≤ 2*‖w‖ := hsep.trans (normalDistance_le_perpendicular hu hv)
  have hw : 0 < ‖w‖ := by linarith
  let e := normalize w
  have he : ‖e‖ = 1 := by
    dsimp [e,NormedSpace.normalize]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw),inv_mul_cancel₀ hw.ne']
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have hwu : inner ℝ u w = 0 := by
    simp only [w,perpendicularPart,inner_sub_right,inner_smul_right,huu,mul_one,sub_self]
  have heu : inner ℝ u e = 0 := by
    simp only [e,NormedSpace.normalize,inner_smul_right,hwu,mul_zero]
  have horth : Orthonormal ℝ (![u,e] : Fin 2 → Space d) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using huu
    · simpa using heu
    · have h : inner ℝ e u = 0 := (real_inner_comm u e).trans heu
      simpa using h
    · simp [he]
  have hc : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  let c := (b-inner ℝ u v*a)/‖w‖
  have hsub : {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ⊆
      {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ e x-c| ≤ 4*r/τ} := by
    intro x hx
    refine ⟨hx.1,?_⟩
    have hformula : inner ℝ e x-c =
        (inner ℝ v x-b-inner ℝ u v*(inner ℝ u x-a))/‖w‖ := by
      simp only [e,NormedSpace.normalize,w,perpendicularPart,real_inner_smul_left,
        inner_sub_left,c]
      ring
    rw [hformula,abs_div,abs_of_pos hw]
    have hb : |inner ℝ v x-b-inner ℝ u v*(inner ℝ u x-a)| ≤ 2*r := by
      apply (abs_sub _ _).trans
      rw [abs_mul]
      have hmul := mul_le_mul hc hx.1 (abs_nonneg _) zero_le_one
      linarith [hx.2]
    apply (div_le_div_of_nonneg_right hb hw.le).trans
    apply (div_le_div_iff₀ hw hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht hr.le]
  have hR : r ≤ 4*r/τ := by
    apply (le_div_iff₀ hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hτ1 hr.le]
  have hmass := orthonormal_rectangle_mass μ (![u,e] : Fin 2 → Space d)
    horth a c hr hR hC hplane
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hmass
  apply (measure_mono hsub).trans (hmass.trans_eq ?_)
  congr 1
  field_simp
  ring

end Falconer

end OAI
