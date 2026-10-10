import OAI.Analysis.CircleDomains.Reflection.CayleyHolomorphic
import Mathlib.Analysis.Complex.Schwarz

namespace OAI

/-! The Schwarz derivative estimate for a map into the upper half-plane.
It controls a boundary logarithm's derivative by its imaginary part,
without requiring a bound on the real part. -/
open Set Function Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

def upperHalfPlaneFractional (a w : ℂ) : ℂ := (w-a)/(w-conj a)

lemma upperHalfPlaneFractional_den {a w : ℂ} (ha : 0<a.im) (hw : 0<w.im) :
    w-conj a≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [sub_im,conj_im,zero_im] at hi
  linarith

lemma upperHalfPlaneFractional_norm_lt {a w : ℂ} (ha : 0<a.im) (hw : 0<w.im) :
    ‖upperHalfPlaneFractional a w‖<1 := by
  have hsq : ‖w-conj a‖^2-‖w-a‖^2=4*w.im*a.im := by
    simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,sub_re,sub_im,conj_re,conj_im]
    ring
  have hlt : ‖w-a‖<‖w-conj a‖ := by
    nlinarith [mul_pos hw ha,norm_nonneg (w-a),norm_nonneg (w-conj a)]
  rw [upperHalfPlaneFractional,norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (upperHalfPlaneFractional_den ha hw))).mpr hlt

lemma upperHalfPlaneFractional_hasDerivAt {a w : ℂ} (ha : 0<a.im) (hw : 0<w.im) :
    HasDerivAt (upperHalfPlaneFractional a)
      ((a-conj a)/(w-conj a)^2) w := by
  have h : HasDerivAt (fun u : ℂ => (u-a)/(u-conj a))
      ((1*(w-conj a)-(w-a)*1)/(w-conj a)^2) w :=
    ((hasDerivAt_id w).sub_const a).div
      ((hasDerivAt_id w).sub_const (conj a)) (upperHalfPlaneFractional_den ha hw)
  have he : 1*(w-conj a)-(w-a)*1=a-conj a := by ring
  rw [he] at h
  exact h

lemma norm_sub_conj {a : ℂ} (ha : 0≤a.im) : ‖a-conj a‖=2*a.im := by
  have he : a-conj a=((2*a.im : ℝ) : ℂ)*I := by
    apply Complex.ext
    · simp
    · simp;ring
  rw [he,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) ha)]

lemma norm_deriv_le_of_mapsTo_upper {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0<r) (hd : DifferentiableOn ℂ f (ball z r))
    (hmap : ∀w∈ball z r,0<(f w).im) : ‖deriv f z‖≤2*(f z).im/r := by
  let a := f z
  have ha : 0<a.im := hmap z (mem_ball_self hr)
  let T : ℂ → ℂ := upperHalfPlaneFractional a ∘ f
  have hTd : DifferentiableOn ℂ T (ball z r) := by
    intro w hw
    exact ((upperHalfPlaneFractional_hasDerivAt ha (hmap w hw)).differentiableAt.comp w
      ((hd w hw).differentiableAt (isOpen_ball.mem_nhds hw))).differentiableWithinAt
  have hT0 : T z=0 := by simp [T,upperHalfPlaneFractional,a]
  have hTm : MapsTo T (ball z r) (closedBall (T z) 1) := by
    intro w hw
    rw [hT0,mem_closedBall_zero_iff]
    exact (upperHalfPlaneFractional_norm_lt ha (hmap w hw)).le
  have hTder : HasDerivAt T (deriv f z/(a-conj a)) z := by
    convert (upperHalfPlaneFractional_hasDerivAt ha ha).comp z
      ((hd z (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt using 1
    field_simp [upperHalfPlaneFractional_den ha ha]
  have hb := norm_deriv_le_div_of_mapsTo_ball hTd hTm hr
  rw [hTder.deriv,norm_div,norm_sub_conj ha.le] at hb
  have hmul := (div_le_div_iff₀ (by positivity : 0<2*a.im) hr).mp hb
  apply (le_div_iff₀ hr).mpr
  simpa only [one_mul] using hmul

end CircleDomainRigidity

end

end OAI
