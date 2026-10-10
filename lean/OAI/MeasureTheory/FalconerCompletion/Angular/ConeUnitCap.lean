import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierPolynomialSmoothing

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma cone_unit_cap {z w : V} (hz : ‖z‖=1) (hw : ‖w‖=1) :
    dist w z ≤ 2*‖graphPerpND w z‖ ∨ dist w (-z) ≤ 2*‖graphPerpND w z‖ := by
  have hi : |inner ℝ z w| ≤ 1 := by simpa [hz,hw] using abs_real_inner_le_norm z w
  have hp : ‖graphPerpND w z‖^2 = 1-(inner ℝ z w)^2 := by
    rw [graphPerpND,norm_sub_sq_real,norm_smul,inner_smul_right,hz,hw,Real.norm_eq_abs]
    simp only [mul_one,one_pow,sq_abs]
    ring
  have hd : dist w z ^ 2 = 2-2*inner ℝ z w := by
    rw [dist_eq_norm,norm_sub_sq_real,hz,hw,real_inner_comm]
    ring
  have hd' : dist w (-z) ^ 2 = 2+2*inner ℝ z w := by
    rw [dist_eq_norm,norm_sub_sq_real,norm_neg,hz,hw,inner_neg_right,real_inner_comm]
    ring
  rcases le_total 0 (inner ℝ z w) with hs | hs
  · left
    have hh := (abs_le.mp hi).2
    nlinarith [sq_nonneg (1-inner ℝ z w),dist_nonneg (x:=w) (y:=z),norm_nonneg (graphPerpND w z),
      mul_nonneg hs (sub_nonneg.mpr hh)]
  · right
    have hh := (abs_le.mp hi).1
    nlinarith [sq_nonneg (1+inner ℝ z w),dist_nonneg (x:=w) (y:=(-z)),norm_nonneg (graphPerpND w z),
      mul_nonpos_of_nonpos_of_nonneg hs (by linarith : 0 ≤ 1+inner ℝ z w)]

lemma cone_cap_cover {v : V} (hv : v ≠ 0) {W : ℝ} (hW : 0 < W) :
    {w | ‖w‖=1 ∧ ‖graphPerpND w v‖ ≤ W} ⊆
      ball (‖v‖⁻¹ • v) (3*W/‖v‖) ∪ ball (-(‖v‖⁻¹ • v)) (3*W/‖v‖) := by
  intro w hw
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hz : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hnv.ne']
  have he : graphPerpND w (‖v‖⁻¹ • v) = ‖v‖⁻¹ • graphPerpND w v := by
    simp only [graphPerpND,real_inner_smul_left,smul_sub,smul_smul]
  have hb : 2*‖graphPerpND w (‖v‖⁻¹ • v)‖ < 3*W/‖v‖ := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
    have hh := mul_le_mul_of_nonneg_left hw.2 (show 0 ≤ ‖v‖⁻¹ by positivity)
    have hp : 0 < W/‖v‖ := by positivity
    simp only [div_eq_mul_inv] at *
    nlinarith
  rcases cone_unit_cap hz hw.1 with hc | hc
  · exact Or.inl (mem_ball.mpr (hc.trans_lt hb))
  · exact Or.inr (mem_ball.mpr (hc.trans_lt hb))
end GraphLiteralSupport.CurrentFalconer.Exceptional
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V]

omit [InnerProductSpace ℝ V] in
lemma cap_mass_large_radius (ξ : Measure V) {L S R r : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S)
    (hmass : ξ univ ≤ 1) (hc : ∀ w : V, ‖w‖=1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ξ (ball w r) ≤ ENNReal.ofReal (L*r^S)) (w : V) (hw : ‖w‖=1) (hr : R⁻¹ ≤ r) :
    ξ (ball w r) ≤ ENNReal.ofReal (L*r^S) := by
  by_cases hr1 : r ≤ 1
  · exact hc w hw r hr hr1
  · have hh : 1 ≤ L*r^S := one_le_mul_of_one_le_of_one_le hL (Real.one_le_rpow (by linarith) hS)
    exact (measure_mono (subset_univ _)).trans (hmass.trans (by exact_mod_cast ENNReal.ofReal_le_ofReal hh))

lemma cone_mass_bound (ξ : Measure V) {L S R r W : ℝ} (hL : 1 ≤ L) (hS : 0 ≤ S)
    (hmass : ξ univ ≤ 1) (hsphere : ∀ᵐ w ∂ξ, ‖w‖=1)
    (hc : ∀ w : V, ‖w‖=1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ξ (ball w r) ≤ ENNReal.ofReal (L*r^S)) (v : V) (hv : v ≠ 0) (hW : 0 < W)
    (hr : R⁻¹ ≤ r) (hr0 : 0 ≤ r) (hvr : 3*W/‖v‖ ≤ r) :
    ξ {w | ‖graphPerpND w v‖ ≤ W} ≤ ENNReal.ofReal (2*L*r^S) := by
  have hz : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hzn : ‖-(‖v‖⁻¹ • v)‖=1 := by simpa using hz
  calc
    _ ≤ ξ (ball (‖v‖⁻¹ • v) r ∪ ball (-(‖v‖⁻¹ • v)) r) := by
      apply measure_mono_ae
      filter_upwards [hsphere] with w hw
      intro hp
      exact union_subset_union (ball_subset_ball hvr) (ball_subset_ball hvr) (cone_cap_cover hv hW ⟨hw,hp⟩)
    _ ≤ ξ (ball (‖v‖⁻¹ • v) r)+ξ (ball (-(‖v‖⁻¹ • v)) r) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (L*r^S)+ENNReal.ofReal (L*r^S) := add_le_add
      (cap_mass_large_radius ξ hL hS hmass hc _ hz hr)
      (cap_mass_large_radius ξ hL hS hmass hc _ hzn hr)
    _ = _ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end GraphLiteralSupport.CurrentFalconer.Exceptional
end
end

end OAI
