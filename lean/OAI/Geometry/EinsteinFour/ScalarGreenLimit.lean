import OAI.Geometry.EinsteinFour.FlatGreenDeterminant
import OAI.Geometry.EinsteinFour.JacobiSineReference

namespace OAI

/-! The scalar flat-kernel determinant converges to sin(theta)/theta. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix Filter
noncomputable section

theorem tendsto_of_cube_tendsto {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Tendsto (fun x => f x ^ 3) l (nhds (a ^ 3))) : Tendsto f l (nhds a) := by
  have ho : Odd 3 := by decide
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.mp h).1 (b ^ 3) (ho.pow_lt_pow.mpr hb)] with x hx
    exact ho.pow_lt_pow.mp hx
  · intro b hb
    filter_upwards [(tendsto_order.mp h).2 (b ^ 3) (ho.pow_lt_pow.mpr hb)] with x hx
    exact ho.pow_lt_pow.mp hx

theorem scalarGreen_reference_factorization (t : ℝ) (N : ℕ) :
    1 - (3 : ℝ) • scaledFlatGreen t N =
      flatGreen N * referenceMatrix (Real.sqrt 3 * t) N := by
  have hf : flatGreen N * scalarDirichlet N 2 = 1 := by
    rw [flatGreen_eq_inverse]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (flatDirichlet_posDef N).isUnit)
  rw [referenceMatrix_sqrt_three, Matrix.mul_sub, hf, Matrix.mul_smul,
    Matrix.mul_one, scaledFlatGreen, smul_smul]

theorem scalarGreen_reference_det (t : ℝ) (N : ℕ) :
    (1 - (3 : ℝ) • scaledFlatGreen t N).det =
      (referenceMatrix (Real.sqrt 3 * t) N).det / ((N : ℝ) + 1) := by
  rw [scalarGreen_reference_factorization, Matrix.det_mul, flatGreen_eq_inverse,
    Matrix.det_nonsing_inv, flatDirichlet_det, Ring.inverse_eq_inv]
  ring

theorem scalarGreen_determinant_tendsto {t : ℝ} (ht : 0 < t)
    (htop : t < Real.pi / Real.sqrt 3) :
    Tendsto (fun N : ℕ => (1 - (3 : ℝ) • scaledFlatGreen t N).det) atTop
      (nhds (Real.sin (Real.sqrt 3 * t) / (Real.sqrt 3 * t))) := by
  have hθ : 0 < Real.sqrt 3 * t := mul_pos (Real.sqrt_pos.mpr (by norm_num)) ht
  have hθπ : Real.sqrt 3 * t < Real.pi := by
    have h := (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mp htop
    nlinarith
  have hc : Tendsto (fun N : ℕ =>
      ((Real.sqrt 3 * t / (N + 1)) * (referenceMatrix (Real.sqrt 3 * t) N).det) ^ 3)
      atTop (nhds (Real.sin (Real.sqrt 3 * t) ^ 3)) := by
    simpa only [mul_pow] using reference_determinant_tendsto hθ hθπ
  have h := (tendsto_of_cube_tendsto hc).div_const (Real.sqrt 3 * t)
  convert h using 1
  ext N
  rw [scalarGreen_reference_det]
  field_simp

end
end PositiveEinsteinFour.Jacobi

end OAI
