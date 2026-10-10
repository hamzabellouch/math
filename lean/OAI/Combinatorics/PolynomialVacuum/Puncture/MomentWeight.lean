import OAI.Combinatorics.PolynomialVacuum.Puncture.AnalyticObligations

namespace OAI

namespace PolynomialVacuumCylinder
open Real

 

noncomputable def denominatorReferenceWeight (p : ℝ) : ℝ :=
  if p=0 then 2/(3*Real.pi) else p/(4*Real.sinh (3*Real.pi*p/8))

noncomputable def denominatorCorrection (p : ℝ) : ℝ :=
  Real.log (1+1/(2*Real.cosh (Real.pi*p/4)))

private theorem exact_hyperbolic_factor (t : ℝ) :
    2*Real.cosh t*Real.sinh (3*t)* (2*Real.cosh (2*t)) =
      Real.sinh (4*t)*(2*Real.cosh (2*t)+1) := by
  have h3 : Real.sinh (3*t)=Real.sinh t*(2*Real.cosh (2*t)+1) := by
    rw [show 3*t=t+2*t by ring,Real.sinh_add,Real.sinh_two_mul,Real.cosh_two_mul]
    linear_combination Real.sinh t * Real.cosh_sq_sub_sinh_sq t
  rw [h3,show 4*t=2*(2*t) by ring,Real.sinh_two_mul,Real.sinh_two_mul]
  ring

theorem denominatorMomentWeight_factor (p : ℝ) :
    denominatorMomentWeight p = denominatorReferenceWeight p * Real.exp (denominatorCorrection p) := by
  have hc : 0 < 1+1/(2*Real.cosh (Real.pi*p/4)) := by positivity
  rw [denominatorCorrection,Real.exp_log hc]
  by_cases hp : p=0
  · subst p
    simp [denominatorMomentWeight,denominatorReferenceWeight]
    field_simp
    ring
  · rw [denominatorMomentWeight,denominatorReferenceWeight,ite_eq_right hp,ite_eq_right hp]
    have h2 : Real.sinh (Real.pi*p/2)≠0 :=
      Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero hp) (by norm_num))
    have h3 : Real.sinh (3*Real.pi*p/8)≠0 :=
      Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hp) (by norm_num))
    have h4 : Real.cosh (Real.pi*p/4)≠0 := (Real.cosh_pos _).ne'
    have h := exact_hyperbolic_factor (Real.pi*p/8)
    have ha : 2*(Real.pi*p/8)=Real.pi*p/4 := by ring
    have hb : 3*(Real.pi*p/8)=3*Real.pi*p/8 := by ring
    have hd : 4*(Real.pi*p/8)=Real.pi*p/2 := by ring
    rw [ha,hb,hd] at h
    field_simp
    convert h using 1 <;> ring_nf

theorem denominatorReferenceWeight_pos (p : ℝ) : 0<denominatorReferenceWeight p := by
  by_cases hp : p=0
  · subst p
    simpa only [denominatorReferenceWeight,ite_true] using
      (div_pos (by norm_num : (0 : ℝ)<2) (mul_pos (by norm_num : (0 : ℝ)<3) Real.pi_pos))
  · rw [denominatorReferenceWeight,ite_eq_right hp]
    rcases lt_or_gt_of_ne hp with hp|hp
    · apply div_pos_of_neg_of_neg hp
      have h : 3*Real.pi*p/8<0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hp) (by norm_num)
      have hs : Real.sinh (3*Real.pi*p/8)<0 := by
        simpa only [Real.sinh_zero] using (Real.sinh_lt_sinh.mpr h)
      linarith
    · apply div_pos hp
      have h : 0<3*Real.pi*p/8 := by positivity
      exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr h)

theorem denominatorMomentWeight_pos (p : ℝ) : 0<denominatorMomentWeight p := by
  rw [denominatorMomentWeight_factor]
  exact mul_pos (denominatorReferenceWeight_pos p) (Real.exp_pos _)

theorem denominatorCorrection_pos (p : ℝ) : 0<denominatorCorrection p := by
  apply Real.log_pos
  have h : 0<1/(2*Real.cosh (Real.pi*p/4)) := by positivity
  linarith

theorem denominatorCorrection_even (p : ℝ) :
    denominatorCorrection (-p)=denominatorCorrection p := by
  simp [denominatorCorrection,neg_div]

theorem denominatorCorrection_continuous : Continuous denominatorCorrection := by
  unfold denominatorCorrection
  apply Continuous.log
  · have h : Continuous (fun p : ℝ=>2*Real.cosh (Real.pi*p/4)) := by fun_prop
    exact continuous_const.add (continuous_const.div h (fun p=>mul_ne_zero (by norm_num) (Real.cosh_pos _).ne'))
  · intro p
    have : 0<1+1/(2*Real.cosh (Real.pi*p/4)) := by positivity
    exact this.ne'

theorem denominatorCorrection_decay (p : ℝ) :
    denominatorCorrection p ≤ Real.exp (-(Real.pi/4)*|p|) := by
  have hcos : Real.cosh (Real.pi*p/4)=Real.cosh (Real.pi*|p|/4) := by
    rcases le_total 0 p with hp|hp
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hp]
      simp [neg_div]
  have hlog := Real.log_le_sub_one_of_pos
    (show 0<1+1/(2*Real.cosh (Real.pi*p/4)) by positivity)
  have hden : Real.exp (Real.pi*|p|/4)≤2*Real.cosh (Real.pi*p/4) := by
    rw [hcos,Real.cosh_eq]
    have := (Real.exp_pos (-(Real.pi*|p|/4))).le
    linarith
  calc
    denominatorCorrection p ≤ 1/(2*Real.cosh (Real.pi*p/4)) := by
      unfold denominatorCorrection
      linarith
    _ ≤ 1/Real.exp (Real.pi*|p|/4) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hden
    _ = Real.exp (-(Real.pi/4)*|p|) := by
      rw [one_div,←Real.exp_neg]
      congr 1
      ring

end PolynomialVacuumCylinder

end OAI
