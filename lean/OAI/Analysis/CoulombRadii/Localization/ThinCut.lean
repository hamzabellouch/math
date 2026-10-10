import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma transition_derivative_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (K:=Set.Icc (0:ℝ) 1) isCompact_Icc
  intro x hx
  rcases not_and_or.mp hx with h|h
  · have hx0 : x<0 := lt_of_not_ge h
    have H : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds hx0] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [H.deriv_eq]
    simp
  · have hx1 : 1<x := lt_of_not_ge h
    have H : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
      filter_upwards [eventually_gt_nhds hx1] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [H.deriv_eq]
    simp

lemma transition_derivative_bounded : ∃ C : ℝ, 0<C ∧ ∀ x, |deriv Real.smoothTransition x|≤C := by
  obtain ⟨B,hB⟩ := transition_derivative_compact.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff (n:=1)).continuous_deriv_one)
  exact ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x =>
    (by simpa only [Real.norm_eq_abs] using (hB x).trans (le_max_left B 1))⟩

def transitionDerivativeBound : ℝ := Classical.choose transition_derivative_bounded
lemma transitionDerivativeBound_pos : 0<transitionDerivativeBound :=
  (Classical.choose_spec transition_derivative_bounded).1
lemma transition_derivative_bound (x : ℝ) : |deriv Real.smoothTransition x|≤transitionDerivativeBound :=
  (Classical.choose_spec transition_derivative_bounded).2 x

def thinAngle (y : Space) (t b : ℝ) (x : Space) : ℝ :=
  (Real.pi/2)*Real.smoothTransition (((t+b)^2-‖x-y‖^2)/((t+b)^2-t^2))

lemma thinAngle_smooth (y : Space) (t b : ℝ) : ContDiff ℝ ∞ (thinAngle y t b) := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const _))

lemma thinAngle_fderiv (y : Space) (t b : ℝ) (x v : Space) :
    fderiv ℝ (thinAngle y t b) x v =
      -Real.pi*deriv Real.smoothTransition (((t+b)^2-‖x-y‖^2)/((t+b)^2-t^2))*
        inner ℝ (x-y) v/((t+b)^2-t^2) := by
  have Hf := (((((hasFDerivAt_id x).sub_const y).norm_sq).const_sub ((t+b)^2)).const_mul ((t+b)^2-t^2)⁻¹)
  have Hfun : (fun z : Space => ((t+b)^2-t^2)⁻¹ * ((t+b)^2-‖id z-y‖^2)) =
      (fun z : Space => ((t+b)^2-‖z-y‖^2)/((t+b)^2-t^2)) := by
    funext z
    simp only [id_eq,div_eq_mul_inv,mul_comm]
  rw [Hfun] at Hf
  have Hg := (((Real.smoothTransition.contDiff (n:=1)).differentiable (by simp) _).hasDerivAt.comp_hasFDerivAt x Hf).const_mul (Real.pi/2)
  have H := congrArg (fun L : Space →L[ℝ] ℝ => L v) Hg.fderiv
  change fderiv ℝ (thinAngle y t b) x v = _ at H
  rw [H]
  simp only [smul_apply,neg_apply,
    smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    innerSL_apply_apply,id_eq]
  ring

lemma thinAngle_core (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : ‖x-y‖≤t) : thinAngle y t b x=Real.pi/2 := by
  have hd : 0<(t+b)^2-t^2 := by nlinarith
  unfold thinAngle
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ hd]
    nlinarith [norm_nonneg (x-y)]

lemma thinAngle_exterior (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : t+b≤‖x-y‖) : thinAngle y t b x=0 := by
  have hd : 0<(t+b)^2-t^2 := by nlinarith
  unfold thinAngle
  rw [Real.smoothTransition.zero_of_nonpos,mul_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x-y)]) hd.le

lemma thinAngle_fderiv_exterior (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    {x : Space} (hx : t+b<‖x-y‖) : fderiv ℝ (thinAngle y t b) x=0 := by
  have H : thinAngle y t b =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    have hh : ∀ᶠ z in 𝓝 x, t+b < ‖z-y‖ :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
    filter_upwards [hh] with z hz
    exact thinAngle_exterior y ht hb z hz.le
  rw [H.fderiv_eq]
  simp

def thinCutCoefficient : ℝ := Real.pi*transitionDerivativeBound
lemma thinCutCoefficient_pos : 0<thinCutCoefficient := mul_pos Real.pi_pos transitionDerivativeBound_pos

lemma thinAngle_derivative_bound (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (i : Fin 3) (x : Space) :
    |fderiv ℝ (thinAngle y t b) x (EuclideanSpace.single i 1)| ≤ thinCutCoefficient/b := by
  by_cases hx : ‖x-y‖≤t+b
  · have hd : 0<(t+b)^2-t^2 := by nlinarith
    rw [thinAngle_fderiv,abs_div,abs_mul,abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_of_pos hd]
    have hi : |inner ℝ (x-y) (EuclideanSpace.single i 1)|≤‖x-y‖ := by
      simpa only [PiLp.norm_single,norm_one,mul_one] using abs_real_inner_le_norm (x-y) (EuclideanSpace.single i 1)
    calc
      _ ≤ Real.pi*transitionDerivativeBound*‖x-y‖/((t+b)^2-t^2) := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left (transition_derivative_bound _) Real.pi_pos.le)
          hi (abs_nonneg _) (mul_nonneg Real.pi_pos.le transitionDerivativeBound_pos.le)
      _ ≤ thinCutCoefficient/b := by
        rw [div_le_div_iff₀ hd hb]
        unfold thinCutCoefficient
        have hc := thinCutCoefficient_pos.le
        unfold thinCutCoefficient at hc
        have hh : ‖x-y‖*b≤(t+b)^2-t^2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hh hc]
  · rw [thinAngle_fderiv_exterior y ht hb (lt_of_not_ge hx)]
    simp only [zero_apply,abs_zero]
    exact div_nonneg thinCutCoefficient_pos.le hb.le

def thinCut (y : Space) (t b : ℝ) (l : Fin 2) (x : Space) : ℝ :=
  if l=0 then Real.sin (thinAngle y t b x) else Real.cos (thinAngle y t b x)
lemma thinCut_smooth (y : Space) (t b : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (thinCut y t b l) := by
  unfold thinCut
  split_ifs
  · exact (thinAngle_smooth y t b).sin
  · exact (thinAngle_smooth y t b).cos
lemma thinCut_partition (y : Space) (t b : ℝ) (x : Space) : ∑ l : Fin 2, thinCut y t b l x^2=1 := by
  simp [Fin.sum_univ_two,thinCut]
lemma thinCut_core_zero (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : ‖x-y‖≤t) : thinCut y t b 1 x=0 := by
  simp only [thinCut,show (1:Fin 2)≠0 by decide,ite_false,thinAngle_core y ht hb x hx,Real.cos_pi_div_two]
lemma thinCut_out_zero (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (x : Space) (hx : t+b≤‖x-y‖) : thinCut y t b 0 x=0 := by
  simp [thinCut,thinAngle_exterior y ht hb x hx]
lemma thinCut_derivative_bound (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (l : Fin 2) (i : Fin 3) (x : Space) :
    |fderiv ℝ (thinCut y t b l) x (EuclideanSpace.single i 1)| ≤ thinCutCoefficient/b := by
  have H := thinAngle_derivative_bound y ht hb i x
  unfold thinCut
  split_ifs
  · rw [fderiv_sin ((thinAngle_smooth y t b).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using H)
  · rw [fderiv_cos ((thinAngle_smooth y t b).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using H)

end Coulomb
end

end
end

end OAI
