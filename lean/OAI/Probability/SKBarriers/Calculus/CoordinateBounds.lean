import Mathlib
import OAI.Probability.SKBarriers.Calculus.HessianBounds

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem norm_sq_le_parameter_sq_add_coordinateSquare (n : ℕ) (z : ParameterSpace n) :
    ‖z‖^2 ≤ (parameter n z)^2 + coordinateSquare n z := by
  induction n with
  | zero => simp [coordinateSquare, parameter, Real.norm_eq_abs, sq_abs]
  | succ n ih =>
    change ‖(z.1,z.2)‖^2 ≤ (parameter n z.1)^2 + (coordinateSquare n z.1+z.2^2)
    rw [Prod.norm_def, max_def]
    split_ifs with hh
    · rw [Real.norm_eq_abs, sq_abs]
      nlinarith [coordinateSquare_nonneg n z.1, sq_nonneg (parameter n z.1)]
    · nlinarith [ih z.1, sq_nonneg z.2]

theorem ae_parameter_eq (n : ℕ) (x : ℝ) :
    ∀ᵐ z ∂fiberMeasure n x, parameter n z = x := by
  induction n with
  | zero => simp [fiberMeasure, parameter]
  | succ n ih =>
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      ((isClosed_eq (parameter (n+1)).continuous continuous_const).measurableSet)).mpr
    filter_upwards [ih] with z hz
    exact ae_of_all _ (fun _ => hz)

theorem potential_gaussian_lower (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {c : ℝ} (hc : 0 < c)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    (z : ParameterSpace n) (hz : parameter n z = 0) :
    V 0 - ‖fderiv ℝ V 0‖^2/c + c/4*coordinateSquare n z ≤ V z := by
  have ht := hessian_tangent_lower V hV 0 z (fun t => hH (0+t • z) z)
  rw [zero_add] at ht
  have hn := norm_sq_le_parameter_sq_add_coordinateSquare n z
  rw [hz, zero_pow (by omega : 2 ≠ 0), zero_add] at hn
  have hop := (fderiv ℝ V 0).le_opNorm z
  rw [Real.norm_eq_abs] at hop
  have hlo := (neg_le_abs (fderiv ℝ V 0 z)).trans hop
  have hy : ‖fderiv ℝ V 0‖*‖z‖ ≤ ‖fderiv ℝ V 0‖^2/c + c/4*coordinateSquare n z := by
    have hs : 0 ≤ (‖fderiv ℝ V 0‖ - c/2*‖z‖)^2/c := div_nonneg (sq_nonneg _) hc.le
    have he : (‖fderiv ℝ V 0‖ - c/2*‖z‖)^2/c =
        ‖fderiv ℝ V 0‖^2/c - ‖fderiv ℝ V 0‖*‖z‖ + c/4*‖z‖^2 := by
      field_simp
      ring
    rw [he] at hs
    nlinarith
  linarith

theorem continuous_coordinateSquare (n : ℕ) : Continuous (coordinateSquare n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (ih.comp continuous_fst).add (continuous_snd.pow 2)

theorem integrable_stronglyConvex_density (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {c : ℝ} (hc : 0 < c)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u) :
    Integrable (fun z => Real.exp (-V z)) (fiberMeasure n 0) ∧
    Integrable (fun z => coordinateSquare n z*Real.exp (-V z)) (fiberMeasure n 0) := by
  let K := Real.exp (‖fderiv ℝ V 0‖^2/c-V 0)
  have hqcont := continuous_coordinateSquare n
  have hbound : ∀ᵐ z ∂fiberMeasure n 0,
      Real.exp (-V z) ≤ K*Real.exp (-(c/4)*coordinateSquare n z) := by
    filter_upwards [ae_parameter_eq n 0] with z hz
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by have := potential_gaussian_lower n V hV hc hH z hz; linarith)
  constructor
  · apply ((integrable_coordinateGaussian n 0 (div_pos hc (by norm_num : (0:ℝ)<4))).const_mul K).mono'
      hV.neg.exp.continuous.aestronglyMeasurable
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz
  · apply ((integrable_coordinateSquare_gaussian n 0 (div_pos hc (by norm_num : (0:ℝ)<4))).const_mul K).mono'
      (hqcont.mul hV.neg.exp.continuous).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    change ‖coordinateSquare n z * Real.exp (-V z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coordinateSquare_nonneg n z) (Real.exp_pos _).le)]
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hz (coordinateSquare_nonneg n z)

end SK.Analytic

end
end
end
end
end

end OAI
