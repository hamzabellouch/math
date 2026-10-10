import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Forms

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
namespace CoulombAtom

lemma smoothTransition_deriv_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hh : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    (eventually_lt_nhds hx).mono fun _ hy => Real.smoothTransition.zero_of_nonpos hy.le
  simpa only [deriv_const] using hh.deriv_eq

lemma smoothTransition_deriv_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hh : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    (eventually_gt_nhds hx).mono fun _ hy => Real.smoothTransition.one_of_one_le hy.le
  simpa only [deriv_const] using hh.deriv_eq

lemma smoothTransition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro x hx
  constructor
  · by_contra h
    exact hx (smoothTransition_deriv_zero_of_neg (lt_of_not_ge h))
  · by_contra h
    exact hx (smoothTransition_deriv_zero_of_one_lt (lt_of_not_ge h))

lemma smoothTransition_deriv_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C,hC⟩ := smoothTransition_deriv_compact.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp))
  refine ⟨1 + |C|, by positivity, fun x => ?_⟩
  exact (hC x).trans (by linarith [le_abs_self C])

def smoothTransitionBound : ℝ := Classical.choose smoothTransition_deriv_bounded

lemma smoothTransitionBound_pos : 0 < smoothTransitionBound :=
  (Classical.choose_spec smoothTransition_deriv_bounded).1

lemma smoothTransition_deriv_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ smoothTransitionBound :=
  (Classical.choose_spec smoothTransition_deriv_bounded).2 x

def radialParameter (y : Space) (t b : ℝ) (x : Space) : ℝ :=
  (‖x-y‖ ^ 2 - t ^ 2) / ((t+b)^2-t^2)

def radialPhase (y : Space) (t b : ℝ) (x : Space) : ℝ :=
  (Real.pi / 2) * Real.smoothTransition (radialParameter y t b x)

lemma radialParameter_regular (y : Space) (t b : ℝ) : ContDiff ℝ ∞ (radialParameter y t b) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const).div_const _

lemma radialPhase_regular (y : Space) (t b : ℝ) : ContDiff ℝ ∞ (radialPhase y t b) :=
  contDiff_const.mul ((Real.smoothTransition.contDiff (n := ⊤)).comp (radialParameter_regular y t b))

lemma radialParameter_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (radialParameter y t b) x v =
      2 * inner ℝ (x-y) v / ((t+b)^2-t^2) := by
  have hh := (((hasFDerivAt_id x).sub_const y).norm_sq.sub_const (t^2)).mul_const (((t+b)^2-t^2)⁻¹)
  change HasFDerivAt (radialParameter y t b) _ x at hh
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
  ring

lemma radialPhase_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (radialPhase y t b) x v =
      (Real.pi / 2) * deriv Real.smoothTransition (radialParameter y t b x) *
        (2 * inner ℝ (x-y) v / ((t+b)^2-t^2)) := by
  have hp := (radialParameter_regular y t b).differentiable (by simp) x
  have hs := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    (radialParameter y t b x)).hasDerivAt
  have hh := (hs.comp_hasFDerivAt x hp.hasFDerivAt).const_mul (Real.pi/2)
  change HasFDerivAt (radialPhase y t b) _ x at hh
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [← hp.lineDeriv_eq_fderiv, radialParameter_derivative]
  ring

lemma radial_denominator_pos {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    0 < (t+b)^2-t^2 := by nlinarith

lemma radialPhase_derivative_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (radialPhase y t b) x (spaceDirections a)| ≤
      Real.pi * smoothTransitionBound / b := by
  rw [radialPhase_derivative]
  have hD := radial_denominator_pos ht hb
  have hC := smoothTransitionBound_pos
  by_cases hlow : radialParameter y t b x < 0
  · rw [smoothTransition_deriv_zero_of_neg hlow]
    simp only [mul_zero, zero_mul, abs_zero]
    positivity
  by_cases hhigh : 1 < radialParameter y t b x
  · rw [smoothTransition_deriv_zero_of_one_lt hhigh]
    simp only [mul_zero, zero_mul, abs_zero]
    positivity
  have hr : ‖x-y‖ ≤ t+b := by
    have hh : (‖x-y‖ ^ 2 - t^2) ≤ (t+b)^2-t^2 :=
      (div_le_one hD).mp (le_of_not_gt hhigh)
    nlinarith [norm_nonneg (x-y)]
  have hi : |inner ℝ (x-y) (spaceDirections a)| ≤ t+b := by
    calc
      _ ≤ ‖x-y‖ * ‖spaceDirections a‖ := by simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (x-y) (spaceDirections a))
      _ = ‖x-y‖ := by simp [spaceDirections]
      _ ≤ t+b := hr
  have hd : |2 * inner ℝ (x-y) (spaceDirections a) / ((t+b)^2-t^2)| ≤
      2 * (t+b) / ((t+b)^2-t^2) := by
    rw [abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hD.le
  rw [abs_mul, abs_mul, abs_of_pos (div_pos Real.pi_pos (by norm_num))]
  calc
    _ ≤ ((Real.pi / 2) * smoothTransitionBound) * (2 * (t+b) / ((t+b)^2-t^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (smoothTransition_deriv_le _) (by positivity))
        hd (abs_nonneg _) (by positivity)
    _ = (Real.pi * smoothTransitionBound) * ((t+b) / ((t+b)^2-t^2)) := by ring
    _ ≤ (Real.pi * smoothTransitionBound) * (1/b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_div_iff₀ hD hb).mpr
      nlinarith [mul_nonneg ht hb.le]
    _ = _ := by ring

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
