import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpatialErrorWeight
import OAI.Analysis.CoulombIonization.Variational.SmoothTransitionBound

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma radial_cos_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (fun z => Real.cos (radialPhase y t b z)) x v =
      -Real.sin (radialPhase y t b x) * lineDeriv ℝ (radialPhase y t b) x v := by
  have h := (radialPhase_regular y t b).differentiable (by simp) x
  rw [h.hasFDerivAt.cos.differentiableAt.lineDeriv_eq_fderiv, h.hasFDerivAt.cos.fderiv,
    h.lineDeriv_eq_fderiv]
  simp only [smul_apply, smul_eq_mul]

lemma radial_sin_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (fun z => Real.sin (radialPhase y t b z)) x v =
      Real.cos (radialPhase y t b x) * lineDeriv ℝ (radialPhase y t b) x v := by
  have h := (radialPhase_regular y t b).differentiable (by simp) x
  rw [h.hasFDerivAt.sin.differentiableAt.lineDeriv_eq_fderiv, h.hasFDerivAt.sin.fderiv,
    h.lineDeriv_eq_fderiv]
  simp only [smul_apply, smul_eq_mul]

def radialInside (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    SmoothMultiplier spaceDirections where
  value x := Real.cos (radialPhase y t b x)
  regular := (radialPhase_regular y t b).cos
  bound := ⟨1, fun x => Real.abs_cos_le_one _⟩
  gradient_bound := by
    intro a
    refine ⟨Real.pi * smoothTransitionBound / b, fun x => ?_⟩
    rw [radial_cos_derivative, abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)

def radialOutside (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    SmoothMultiplier spaceDirections where
  value x := Real.sin (radialPhase y t b x)
  regular := (radialPhase_regular y t b).sin
  bound := ⟨1, fun x => Real.abs_sin_le_one _⟩
  gradient_bound := by
    intro a
    refine ⟨Real.pi * smoothTransitionBound / b, fun x => ?_⟩
    rw [radial_sin_derivative, abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)

def radialCut (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    Fin 2 → SmoothMultiplier spaceDirections :=
  ![radialInside y ht hb, radialOutside y ht hb]

lemma radialCut_partition (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) : ∑ h : Fin 2, (radialCut y ht hb h).value x ^ 2 = 1 := by
  simpa only [Fin.sum_univ_two, radialCut, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, radialInside, radialOutside, add_comm] using
    Real.sin_sq_add_cos_sq (radialPhase y t b x)

lemma radialPhase_zero {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : ‖x-y‖ ≤ t) : radialPhase y t b x = 0 := by
  have hp : radialParameter y t b x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x-y)])
      (radial_denominator_pos ht hb).le
  simp only [radialPhase, Real.smoothTransition.zero_of_nonpos hp, mul_zero]

lemma radialPhase_pi_half {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : t+b ≤ ‖x-y‖) : radialPhase y t b x = Real.pi/2 := by
  have hp : 1 ≤ radialParameter y t b x := by
    apply (one_le_div (radial_denominator_pos ht hb)).mpr
    nlinarith [norm_nonneg (x-y)]
  simp only [radialPhase, Real.smoothTransition.one_of_one_le hp, mul_one]

lemma radialCut_inner {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : ‖x-y‖ ≤ t) :
    (radialCut y ht hb 0).value x = 1 ∧ (radialCut y ht hb 1).value x = 0 := by
  simp [radialCut, radialInside, radialOutside, radialPhase_zero ht hb hx]

lemma radialCut_outer {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : t+b ≤ ‖x-y‖) :
    (radialCut y ht hb 0).value x = 0 ∧ (radialCut y ht hb 1).value x = 1 := by
  simp [radialCut, radialInside, radialOutside, radialPhase_pi_half ht hb hx]

lemma radialCut_local_error (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) :
    spatialErrorWeight (radialCut y ht hb) x =
      ∑ a : Fin 3, lineDeriv ℝ (radialPhase y t b) x (spaceDirections a) ^ 2 := by
  unfold spatialErrorWeight
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.sum_univ_two, radialCut, Matrix.cons_val_zero, Matrix.cons_val_one,
    radialInside, radialOutside, radial_cos_derivative, radial_sin_derivative]
  nlinarith [Real.sin_sq_add_cos_sq (radialPhase y t b x)]

lemma radialPhase_derivative_zero_off_collar {y x : Space} {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hx : ¬ (t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b)) (v : Space) :
    lineDeriv ℝ (radialPhase y t b) x v = 0 := by
  rw [radialPhase_derivative]
  have hD := radial_denominator_pos ht hb
  have hs : deriv Real.smoothTransition (radialParameter y t b x) = 0 := by
    by_cases hlow : ‖x-y‖ < t
    · apply smoothTransition_deriv_zero_of_neg
      apply div_neg_of_neg_of_pos _ hD
      nlinarith [norm_nonneg (x-y)]
    · have hhigh : t+b < ‖x-y‖ := lt_of_not_ge (fun h => hx ⟨le_of_not_gt hlow,h⟩)
      apply smoothTransition_deriv_zero_of_one_lt
      apply (one_lt_div hD).mpr
      nlinarith [norm_nonneg (x-y)]
  rw [hs, mul_zero, zero_mul]

theorem radialCut_error_bound (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) :
    spatialErrorWeight (radialCut y ht hb) x ≤
      (3 * (Real.pi * smoothTransitionBound / b)^2) *
        (if t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b then (1:ℝ) else 0) := by
  classical
  rw [radialCut_local_error]
  by_cases hx : t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b
  · simp only [ite_eq_left hx, mul_one]
    calc
      _ ≤ ∑ a : Fin 3, (Real.pi * smoothTransitionBound / b)^2 := by
        apply Finset.sum_le_sum
        intro a _
        have hC : 0 < Real.pi * smoothTransitionBound / b :=
          div_pos (mul_pos Real.pi_pos smoothTransitionBound_pos) hb
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hC.le).mpr (radialPhase_derivative_le y ht hb x a)
      _ = _ := by simp
  · simp only [ite_eq_right hx, mul_zero]
    simp only [radialPhase_derivative_zero_off_collar ht hb hx, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, le_refl]

end CoulombAtom

open scoped BigOperators

end

end OAI
