import Mathlib
import OAI.Probability.SKGap.Localization.PhiBounds

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

def hyper (b : Bool) (x : ℝ) : ℝ := if b then Real.sinh x else Real.cosh x
lemma continuous_hyper (b : Bool) : Continuous (hyper b) := by unfold hyper; split_ifs <;> fun_prop
lemma hyper_hasDerivAt (b : Bool) (x : ℝ) : HasDerivAt (hyper b) (hyper (!b) x) x := by
  cases b <;> simpa only [hyper,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using
    (show HasDerivAt _ _ x from (by first | exact Real.hasDerivAt_cosh x | exact Real.hasDerivAt_sinh x))

lemma hyper_abs_le (b : Bool) (x : ℝ) : |hyper b x|≤Real.cosh x := by
  cases b
  · simp only [hyper,Bool.false_eq_true,ite_false,abs_of_pos (Real.cosh_pos _),le_refl]
  · exact abs_sinh_le_cosh x

def momentNum (p q : ℕ) (b : Bool) (d a : ℝ) : ℝ :=
  ∫u in (0:ℝ)..1,weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d)

def moment (p q : ℕ) (b : Bool) (z r a : ℝ) : ℝ :=
  momentNum p q b (z-r) a/(Real.cosh z*Real.cosh r)

lemma moment_base (z r a : ℝ) : moment 0 0 false z r a=phi z r a := by
  rw [phi_eq]
  simp only [moment,momentNum,numerator,pow_zero,mul_one,hyper,Bool.false_eq_true,ite_false]

lemma momentNum_hasDerivAt_d (p q : ℕ) (b : Bool) (d a : ℝ) :
    HasDerivAt (fun d=>momentNum p q b d a) (momentNum (p+1) q (!b) d a) d := by
  unfold momentNum
  apply hasDerivAt_integral01
    (F:=fun d u=>weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d))
    (F':=fun d u=>weight a u*u^(p+1)*((1-u^2)/2)^q*hyper (!b) (u*d))
  · exact (((continuous_weight a).comp continuous_snd).mul (continuous_snd.pow p)|>.mul
      (((continuous_const.sub (continuous_snd.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper b).comp (continuous_snd.mul continuous_fst))
  · exact (((continuous_weight a).comp continuous_snd).mul (continuous_snd.pow (p+1))|>.mul
      (((continuous_const.sub (continuous_snd.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper (!b)).comp (continuous_snd.mul continuous_fst))
  · intro d u
    have H:=((hyper_hasDerivAt b (u*d)).comp d ((hasDerivAt_id d).const_mul u)).const_mul
      (weight a u*u^p*((1-u^2)/2)^q)
    convert! H using 1
    simp only [pow_succ]
    ring

lemma momentNum_hasDerivAt_a (p q : ℕ) (b : Bool) (d a : ℝ) :
    HasDerivAt (fun a=>momentNum p q b d a) (momentNum p (q+1) b d a) a := by
  unfold momentNum
  apply hasDerivAt_integral01
    (F:=fun a u=>weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d))
    (F':=fun a u=>weight a u*u^p*((1-u^2)/2)^(q+1)*hyper b (u*d))
  · apply Continuous.mul
    · unfold weight; fun_prop
    · exact (continuous_hyper b).comp (continuous_snd.mul_const d)
  · apply Continuous.mul
    · unfold weight; fun_prop
    · exact (continuous_hyper b).comp (continuous_snd.mul_const d)
  · intro a u
    have H:=((((hasDerivAt_id a).mul_const (1-u^2)).div_const 2).exp).mul_const
      (u^p*((1-u^2)/2)^q*hyper b (u*d))
    convert! H using 1 <;> (try funext x) <;> dsimp [weight] <;> simp only [pow_succ] <;> ring

lemma momentNum_abs_le (p q : ℕ) (b : Bool) (d a : ℝ) :
    |momentNum p q b d a|≤ momentNum 0 0 false d a := by
  unfold momentNum
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ)≤1)).trans
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
  · apply Continuous.intervalIntegrable
    apply Continuous.abs
    exact (((continuous_weight a).mul (continuous_id.pow p)).mul
      (((continuous_const.sub (continuous_id.pow 2)).div_const 2).pow q)).mul
      ((continuous_hyper b).comp (continuous_id.mul_const d))
  · apply Continuous.intervalIntegrable
    exact (((continuous_weight a).mul (continuous_id.pow 0)).mul
      (((continuous_const.sub (continuous_id.pow 2)).div_const 2).pow 0)).mul
      ((continuous_hyper false).comp (continuous_id.mul_const d))
  · intro u hu
    have hu2 : u^2≤1 := by nlinarith [hu.1,hu.2]
    have hv0 : 0≤(1-u^2)/2 := by linarith
    have hv1 : (1-u^2)/2≤1 := by nlinarith [sq_nonneg u]
    have hp : u^p ≤ 1 := pow_le_one₀ hu.1 hu.2
    have hq : ((1-u^2)/2)^q ≤ 1 := pow_le_one₀ hv0 hv1
    simp only [abs_mul,abs_of_pos (show 0<weight a u from Real.exp_pos _),
      abs_pow,abs_of_nonneg hu.1,abs_of_nonneg hv0,pow_zero,mul_one,
      hyper,Bool.false_eq_true,ite_false]
    have hH:=hyper_abs_le b (u*d)
    change |if b=true then Real.sinh (u*d) else Real.cosh (u*d)|≤Real.cosh (u*d) at hH
    have hprod : u^p*((1-u^2)/2)^q≤1 :=
      (mul_le_mul hp hq (pow_nonneg hv0 q) (by norm_num)).trans_eq (one_mul 1)
    have hh:=mul_le_mul (mul_le_mul_of_nonneg_left hprod (Real.exp_pos (a*(1-u^2)/2)).le)
      hH (abs_nonneg _) (by positivity)
    dsimp [weight] at *
    nlinarith only [hh]

lemma moment_relative_bound (p q : ℕ) (b : Bool) (z r a : ℝ) :
    |moment p q b z r a|≤phi z r a := by
  rw [moment,abs_div,abs_of_pos (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)),←moment_base]
  exact div_le_div_of_nonneg_right (momentNum_abs_le p q b (z-r) a)
    (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le

lemma moment_hasDerivAt_z (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun z=>moment p q b z r a)
      (moment (p+1) q (!b) z r a-Real.tanh z*moment p q b z r a) z := by
  have H:=((momentNum_hasDerivAt_d p q b (z-r) a).comp z ((hasDerivAt_id z).sub_const r)).div
    ((Real.hasDerivAt_cosh z).mul_const (Real.cosh r))
    (ne_of_gt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
  convert! H using 1
  dsimp [moment]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma moment_hasDerivAt_r (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun r=>moment p q b z r a)
      (-moment (p+1) q (!b) z r a-Real.tanh r*moment p q b z r a) r := by
  have H:=((momentNum_hasDerivAt_d p q b (z-r) a).comp r ((hasDerivAt_id r).const_sub z)).div
    ((Real.hasDerivAt_cosh r).const_mul (Real.cosh z))
    (ne_of_gt (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
  convert! H using 1
  dsimp [moment]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos z),ne_of_gt (Real.cosh_pos r)]

lemma moment_hasDerivAt_a (p q : ℕ) (b : Bool) (z r a : ℝ) :
    HasDerivAt (fun a=>moment p q b z r a) (moment p (q+1) b z r a) a := by
  exact (momentNum_hasDerivAt_a p q b (z-r) a).div_const _

end SKGap.Stein

end
end

end OAI
