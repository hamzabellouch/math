import Mathlib
import OAI.Analysis.AffineBernstein.ParametricChangeOfCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Exact density change of variables; its Jacobian has exponent one. -/
theorem parametricAreaDensity_comp {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {φ : Space n → Space n} {x : Space n}
    (hX : ContDiffAt ℝ ∞ X (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (ν : E →L[ℝ] ℝ) (ξ : E) (hν : ν.comp (fderiv ℝ X (φ x)) = 0)
    (hH : 0 ≤ (parametricSecondForm X ν (φ x)).det)
    (hJ : (parametricJacobian φ x).det ≠ 0) :
    parametricAreaDensity b (X ∘ φ) ν ξ x =
      |(parametricJacobian φ x).det| * parametricAreaDensity b X ν ξ (φ x) := by
  have hd := parametricSecondForm_comp hX hφ ν hν
  have he : (parametricSecondForm (X ∘ φ) ν x).det =
      |(parametricJacobian φ x).det| ^ 2 * (parametricSecondForm X ν (φ x)).det := by
    rw [hd, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, sq_abs]
    ring
  rw [parametricAreaDensity, he, parametricFrame_comp_det b
    (hX.differentiableAt (by simp)) (hφ.differentiableAt (by simp)) ξ, abs_mul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (sq_nonneg _) hH,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← Real.rpow_natCast_mul (abs_nonneg _) 2]
  have hp : 0 < |(parametricJacobian φ x).det| := abs_pos.mpr hJ
  have hr : (2 : ℝ) * (1 / ((n : ℝ) + 2)) + (n : ℝ) / ((n : ℝ) + 2) = 1 := by
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  have hc := Real.rpow_add hp (2 * (1 / ((n : ℝ) + 2))) ((n : ℝ) / ((n : ℝ) + 2))
  rw [hr, Real.rpow_one] at hc
  unfold parametricAreaDensity
  simp only [Real.rpow_eq_pow]
  calc
    _ = (|(parametricJacobian φ x).det| ^ (2 * (1 / ((n : ℝ) + 2))) *
          |(parametricJacobian φ x).det| ^ ((n : ℝ) / ((n : ℝ) + 2))) *
        ((parametricSecondForm X ν (φ x)).det ^ (1 / ((n : ℝ) + 2)) *
          |b.det (parametricFrame X ξ (φ x))| ^ ((n : ℝ) / ((n : ℝ) + 2))) := by ring_nf
    _ = _ := by rw [← hc]

end AffineBernstein
end

end OAI
