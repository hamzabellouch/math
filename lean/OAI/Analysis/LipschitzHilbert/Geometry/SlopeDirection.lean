import OAI.Analysis.LipschitzHilbert.Estimates.SlopeOrthonormal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! Quantitative normalization of slope directions and the exact
uncertainty-arc condition needed by the Lacey--Li rectangle input. -/

noncomputable section
open scoped BigOperators NNReal
namespace LipschitzHilbert

def slopeDirection (s : ℝ) : Plane := slopeAxes s 0

theorem slopeDirection_norm (s : ℝ) : ‖slopeDirection s‖ = 1 :=
  (slopeAxes s).norm_eq_one 0

theorem slopeDirection_coordinates (s : ℝ) :
    slopeDirection s = WithLp.toLp 2 ![Real.cos (Real.arctan s), Real.sin (Real.arctan s)] := by
  rw [slopeDirection, slopeAxes_apply]
  simp [slopeAxisVectors, Real.cos_arctan, Real.sin_arctan]

theorem slopeDirection_inner (u s : ℝ) :
    inner ℝ (slopeDirection u) (slopeDirection s) = Real.cos (Real.arctan u-Real.arctan s) := by
  rw [slopeDirection_coordinates, slopeDirection_coordinates]
  change (∑ i : Fin 2, (![Real.cos (Real.arctan s), Real.sin (Real.arctan s)] i)*
    (![Real.cos (Real.arctan u), Real.sin (Real.arctan u)] i)) = _
  simp [Fin.sum_univ_two, Real.cos_sub]
  ring

theorem arctan_lipschitz : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro x
  rw [← NNReal.coe_le_coe]
  change ‖deriv Real.arctan x‖ ≤ (1:ℝ)
  rw [Real.deriv_arctan]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity : 0 < 1+x^2)).mpr (by nlinarith [sq_nonneg x])

theorem arctan_sub_le (u s : ℝ) : |Real.arctan u-Real.arctan s| ≤ |u-s| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using arctan_lipschitz.dist_le_mul u s

theorem plane_norm_le_coordinate_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := EuclideanSpace.real_norm_sq_eq z
  simp only [Fin.sum_univ_two] at h
  apply (sq_le_sq₀ (norm_nonneg z) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [h]
  nlinarith [sq_abs (z 0), sq_abs (z 1),
    mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]

theorem slopeDirection_lipschitz : LipschitzWith 2 slopeDirection := by
  apply LipschitzWith.of_dist_le_mul
  intro u s
  rw [dist_eq_norm]
  have hc := Real.abs_cos_sub_cos_le (Real.arctan u) (Real.arctan s)
  have hs := Real.abs_sin_sub_sin_le (Real.arctan u) (Real.arctan s)
  have ha := arctan_sub_le u s
  have hn := plane_norm_le_coordinate_sum (slopeDirection u-slopeDirection s)
  rw [slopeDirection_coordinates, slopeDirection_coordinates] at hn
  change ‖slopeDirection u-slopeDirection s‖ ≤ (2:ℝ)*dist u s
  rw [slopeDirection_coordinates, slopeDirection_coordinates]
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hn
  rw [Real.dist_eq]
  linarith

theorem cos_le_inner_slopeDirection (u s θ : ℝ) (hθ : θ ≤ Real.pi)
    (hclose : |u-s| ≤ θ) :
    Real.cos θ ≤ inner ℝ (slopeDirection u) (slopeDirection s) := by
  rw [slopeDirection_inner, ← Real.cos_abs (Real.arctan u-Real.arctan s)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hθ
    ((arctan_sub_le u s).trans hclose)

end LipschitzHilbert

end

end OAI
