import OAI.MeasureTheory.Falconer.Incidence.GridCount
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-! # Pulling physical tube tests back to transverse coordinates -/

namespace Falconer
variable {d : ℕ}

theorem inverse_coordinate_tube_bound (e : Space d ≃L[ℝ] Space d)
    (v x a : Space d) (j : Fin d) (hj : (e.symm v) j = 0) :
    |(e.symm x) j-(e.symm a) j| ≤
      ‖e.symm.toContinuousLinearMap‖*‖perpendicularPart v (x-a)‖ := by
  have he : (e.symm (perpendicularPart v (x-a))) j = (e.symm x) j-(e.symm a) j := by
    simp only [perpendicularPart,map_sub,map_smul,PiLp.sub_apply,PiLp.smul_apply,
      smul_eq_mul,hj,mul_zero,sub_zero]
  calc
    _ = ‖(e.symm (perpendicularPart v (x-a))) j‖ := by rw [he,Real.norm_eq_abs]
    _ ≤ ‖e.symm (perpendicularPart v (x-a))‖ := PiLp.norm_apply_le _ _
    _ ≤ _ := e.symm.toContinuousLinearMap.le_opNorm _

noncomputable def tripleGridPoint (δ : ℝ) (z : ℤ × ℤ × ℤ) : Space 3 :=
  WithLp.toLp 2 ![δ*(z.1:ℝ),δ*(z.2.1:ℝ),δ*(z.2.2:ℝ)]

@[simp] theorem tripleGridPoint_zero (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 0 = δ*(z.1:ℝ) := rfl

@[simp] theorem tripleGridPoint_one (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 1 = δ*(z.2.1:ℝ) := rfl

@[simp] theorem tripleGridPoint_two (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 2 = δ*(z.2.2:ℝ) := rfl

theorem transverse_grid_coordinate (e : Space 3 ≃L[ℝ] Space 3)
    (v a : Space 3) (z : ℤ × ℤ × ℤ) (j : Fin 3)
    {δ C : ℝ} (hδ : 0 < δ) (hj : (e.symm v) j = 0)
    (htube : ‖perpendicularPart v (e (tripleGridPoint δ z)-a)‖ ≤ C*δ) :
    |tripleGridPoint δ z j/δ-(e.symm a) j/δ| ≤
      ‖e.symm.toContinuousLinearMap‖*C := by
  have hh := inverse_coordinate_tube_bound e v (e (tripleGridPoint δ z)) a j hj
  rw [e.symm_apply_apply] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left htube (norm_nonneg _))
  rw [← sub_div,abs_div,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  nlinarith

end Falconer

end OAI
