import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

private theorem moment_pow_exp {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x^n = Real.exp ((n:ℝ)*Real.log x) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem primeMoment_factorial_sampling_le (k : ℕ) {J : ℝ} (hJ : 0 < J) :
    (k.factorial:ℝ)*(2/J)^k ≤ (2*(k:ℝ)/J)^k := by
  have hf : (k.factorial:ℝ) ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  calc
    _ ≤ (k:ℝ)^k*(2/J)^k := mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

private theorem sampling_ratio_le {J c Z : ℝ} (hJ : 0 < J) (hc : 0 < c) (hZ : 0 < Z)
    (hlog : 0 < Real.log Z) (hcount : c*Z/Real.log Z ≤ J) (k : ℕ) :
    2*(k:ℝ)/J ≤ (2*(k:ℝ)*Real.log Z/c)/Z := by
  have hmul : c*Z ≤ J*Real.log Z := (div_le_iff₀ hlog).mp hcount
  apply (div_le_div_iff₀ hJ hZ).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2*(k:ℝ) by positivity)]

theorem primeMoment_square_coefficient_le {F H J Z T c : ℝ} {k l : ℕ}
    (hF0 : 0 ≤ F) (hH0 : 0 ≤ H) (hJ : 0 < J) (hZ : 1 ≤ Z) (hT : 2 ≤ T)
    (hl : 1 ≤ l) (hk : 1 ≤ k) (hc : 0 < c) (hlog : 0 < Real.log Z)
    (hF : F ≤ Z^430) (hH : H ≤ 2*Z) (hcount : c*Z/Real.log Z ≤ J)
    (hlogT : Real.log Z ≤ 2*T) (hkT : (k:ℝ) ≤ T) (hTc : 8/c ≤ T) :
    F*2^l*(H^k+1)*(k.factorial:ℝ)*(2/J)^k ≤
      Real.exp (430*Real.log Z+2*(l:ℝ)+3*(k:ℝ)*Real.log T) := by
  have hZp : 0 < Z := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hHP : H^k+1 ≤ 2*(2*Z)^k := by
    have hh := pow_le_pow_left₀ hH0 hH k
    have hone : 1 ≤ (2*Z)^k := one_le_pow₀ (by linarith)
    linarith
  have hratio : 4*Z*(k:ℝ)/J ≤ 4*(k:ℝ)*Real.log Z/c := by
    have hm := (div_le_iff₀ hlog).mp hcount
    apply (div_le_div_iff₀ hJ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*(k:ℝ) by positivity)]
  have hklog : (k:ℝ)*Real.log Z ≤ 2*T^2 := by
    have hh := mul_le_mul hkT hlogT hlog.le hT0
    nlinarith
  have hbase : 4*Z*(k:ℝ)/J ≤ T^3 := by
    refine hratio.trans ?_
    calc
      4*(k:ℝ)*Real.log Z/c ≤ (8/c)*T^2 := by
        apply (div_le_iff₀ hc).mpr
        have hid : (8/c)*T^2*c = 8*T^2 := by field_simp
        rw [hid]
        nlinarith
      _ ≤ T*T^2 := mul_le_mul_of_nonneg_right hTc (sq_nonneg T)
      _ = _ := by ring
  have hterm : (H^k+1)*(k.factorial:ℝ)*(2/J)^k ≤ 2*(T^3)^k := by
    calc
      _ = (H^k+1)*((k.factorial:ℝ)*(2/J)^k) := by ring
      _ ≤ (2*(2*Z)^k)*(2*(k:ℝ)/J)^k :=
        mul_le_mul hHP (primeMoment_factorial_sampling_le k hJ) (by positivity) (by positivity)
      _ = 2*(4*Z*(k:ℝ)/J)^k := by rw [mul_assoc,← mul_pow]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) (by norm_num)
  have hcoef : F*2^l*(H^k+1)*(k.factorial:ℝ)*(2/J)^k ≤ Z^430*2^(l+1)*(T^3)^k := by
    calc
      _ = (F*2^l)*((H^k+1)*(k.factorial:ℝ)*(2/J)^k) := by ring
      _ ≤ (Z^430*2^l)*(2*(T^3)^k) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hF (by positivity)) hterm (by positivity)
          (mul_nonneg (hF0.trans hF) (by positivity))
      _ = _ := by rw [pow_succ]; ring
  have htwo : (2:ℝ)^(l+1) ≤ Real.exp (2*(l:ℝ)) := by
    rw [moment_pow_exp (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
    have hlr : (1:ℝ) ≤ l := by exact_mod_cast hl
    have hh := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ ((l+1:ℕ):ℝ) by positivity)
    push_cast at hh ⊢
    nlinarith
  refine hcoef.trans ?_
  calc
    _ ≤ Z^430*Real.exp (2*(l:ℝ))*(T^3)^k := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo (by positivity)) (by positivity)
    _ = _ := by
      rw [← pow_mul, moment_pow_exp hZp, moment_pow_exp hTp,← Real.exp_add,← Real.exp_add]
      congr 1
      push_cast
      ring

theorem primeMoment_sampling_exp_le {J c Z : ℝ} {k : ℕ}
    (hJ : 0 < J) (hc : 0 < c) (hZ : 0 < Z) (hlog : 0 < Real.log Z)
    (hcount : c*Z/Real.log Z ≤ J) (hsmall : 2*(k:ℝ)*Real.log Z/c ≤ Real.sqrt Z) :
    (k.factorial:ℝ)*(2/J)^k ≤ Real.exp (-((k:ℝ)/2)*Real.log Z) := by
  have hratio : 2*(k:ℝ)/J ≤ Z^(-(1/2:ℝ)) := by
    calc
      _ ≤ (2*(k:ℝ)*Real.log Z/c)/Z := sampling_ratio_le hJ hc hZ hlog hcount k
      _ ≤ Real.sqrt Z/Z := div_le_div_of_nonneg_right hsmall hZ.le
      _ = Z^(-(1/2:ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        calc
          Z^(1/2:ℝ)/Z = Z^(1/2:ℝ)/Z^(1:ℝ) := by rw [Real.rpow_one]
          _ = Z^((1/2:ℝ)-1) := (Real.rpow_sub hZ _ _).symm
          _ = _ := by norm_num
  refine (primeMoment_factorial_sampling_le k hJ).trans ?_
  calc
    _ ≤ (Z^(-(1/2:ℝ)))^k := pow_le_pow_left₀ (by positivity) hratio k
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hZ.le,Real.rpow_def_of_pos hZ]
      congr 1
      ring

theorem primeMoment_nonsquare_coefficient_le {F B V J Z c : ℝ} {k l : ℕ}
    (hF0 : 0 ≤ F) (hB0 : 0 ≤ B) (hV0 : 0 ≤ V) (hJ : 0 < J)
    (hZ : 2 ≤ Z) (hl : 1 ≤ l) (hc : 0 < c) (hlog : 0 < Real.log Z)
    (hF : F ≤ Z^430) (hB : B ≤ Z^14) (hV : V ≤ Z^430)
    (hcount : c*Z/Real.log Z ≤ J) (hsmall : 2*(k:ℝ)*Real.log Z/c ≤ Real.sqrt Z) :
    F*2^l*4*B^(2*l)*V^(2*l)*(k.factorial:ℝ)*(2/J)^k ≤
      Real.exp ((430+900*(l:ℝ))*Real.log Z-((k:ℝ)/2)*Real.log Z) := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hp : B^(2*l)*V^(2*l) ≤ Z^(888*l) := by
    calc
      _ ≤ (Z^14)^(2*l)*(Z^430)^(2*l) :=
        mul_le_mul (pow_le_pow_left₀ hB0 hB _) (pow_le_pow_left₀ hV0 hV _) (by positivity) (by positivity)
      _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; omega
  have htwo : (2:ℝ)^l*4 ≤ Z^(12*l) := by
    calc
      (2:ℝ)^l*4 = (2:ℝ)^(l+2) := by rw [pow_add]; norm_num
      _ ≤ Z^(l+2) := pow_le_pow_left₀ (by norm_num) hZ _
      _ ≤ Z^(12*l) := pow_le_pow_right₀ hZ1 (by omega)
  have hfront : F*2^l*4*B^(2*l)*V^(2*l) ≤ Z^(430+900*l) := by
    calc
      _ = F*((2:ℝ)^l*4)*(B^(2*l)*V^(2*l)) := by ring
      _ ≤ Z^430*Z^(12*l)*Z^(888*l) :=
        mul_le_mul (mul_le_mul hF htwo (by positivity) (hF0.trans hF)) hp (by positivity) (by positivity)
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hsample := primeMoment_sampling_exp_le hJ hc hZp hlog hcount hsmall
  calc
    _ = (F*2^l*4*B^(2*l)*V^(2*l))*((k.factorial:ℝ)*(2/J)^k) := by ring
    _ ≤ Z^(430+900*l)*Real.exp (-((k:ℝ)/2)*Real.log Z) :=
      mul_le_mul hfront hsample (by positivity) (by positivity)
    _ = _ := by
      rw [moment_pow_exp hZp,← Real.exp_add]
      congr 1
      push_cast
      ring

end Ostmann.QuadraticCenter

end

end OAI
