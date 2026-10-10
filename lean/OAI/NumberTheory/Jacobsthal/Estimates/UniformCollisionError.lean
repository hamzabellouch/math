import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosSourceCollision

theorem collision_error_bound (z R N n eta C : ℝ) (hz : 1 < z) (hR : 1 < R)
    (hRz : R ≤ z^((1 : ℝ)/100)) (hN : z^((93 : ℝ)/100) ≤ N)
    (heta : 0 < eta) (hC : 0 ≤ C) (hL : 1 ≤ Real.log z)
    (hcount : eta*R/(4*Real.log R) ≤ n) :
    C*R/(n*(Real.log z)^6)+R/(N*(Real.log z)^6) ≤
      4*C/(eta*(Real.log z)^5)+1/z^((92 : ℝ)/100) := by
  have hz0 : 0 < z := by linarith
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hn : 0 < n := (div_pos (mul_pos heta hR0) (mul_pos (by norm_num) hlogR)).trans_le hcount
  have hNp : 0 < N := (Real.rpow_pos_of_pos hz0 _).trans_le hN
  have hLp : 0 < Real.log z := by linarith
  have hRle : R ≤ z := by
    apply hRz.trans
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (1 : ℝ)/100 ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hlogs : Real.log R ≤ Real.log z := Real.log_le_log hR0 hRle
  have hprim := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlogR)).mp hcount
  have hratio : R/n ≤ 4*Real.log z/eta := by
    apply (div_le_div_iff₀ hn heta).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlogs hn.le]
  have hfirst : C*R/(n*(Real.log z)^6) ≤ 4*C/(eta*(Real.log z)^5) := by
    calc
      _ = C*(R/n)/(Real.log z)^6 := by ring
      _ ≤ C*(4*Real.log z/eta)/(Real.log z)^6 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) (by positivity)
      _ = _ := by field_simp
  have hpow : 0 < z^((92 : ℝ)/100) := Real.rpow_pos_of_pos hz0 _
  have hRN : R/N ≤ 1/z^((92 : ℝ)/100) := by
    apply (div_le_div_iff₀ hNp hpow).mpr
    calc
      R*z^((92 : ℝ)/100) ≤ z^((1 : ℝ)/100)*z^((92 : ℝ)/100) := mul_le_mul_of_nonneg_right hRz hpow.le
      _ = z^((93 : ℝ)/100) := by rw [← Real.rpow_add hz0];norm_num
      _ ≤ 1*N := by simpa only [one_mul] using hN
  have hden : N ≤ N*(Real.log z)^6 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hL : 1 ≤ (Real.log z)^6) hNp.le
    simpa only [mul_one] using hh
  have hsecond : R/(N*(Real.log z)^6) ≤ 1/z^((92 : ℝ)/100) :=
    (div_le_div_of_nonneg_left hR0.le hNp hden).trans hRN
  exact add_le_add hfirst hsecond

end ErdosSourceCollision

end

section

open Filter
open scoped Topology
namespace ErdosSourceCollision

theorem uniform_collision_error (C eta eps : ℝ) (hC : 0 ≤ C) (heta : 0 < eta) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ 1 ≤ Real.log z ∧ ∀ R N n : ℝ,
      1 < R → R ≤ z^((1 : ℝ)/100) → z^((93 : ℝ)/100) ≤ N →
      eta*R/(4*Real.log R) ≤ n →
      C*R/(n*(Real.log z)^6)+R/(N*(Real.log z)^6) ≤ eps^2 := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (8*C/(eta*eps^2)))
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 92/100)).eventually_ge_atTop (2/eps^2)
  filter_upwards [hlog,hpow,eventually_gt_atTop (1 : ℝ)] with z hzL hzpow hz
  have hL : 1 ≤ Real.log z := (le_max_left _ _).trans hzL
  have hL0 : 0 < Real.log z := by linarith
  have hz0 : 0 < z := by linarith
  have he2 : 0 < eps^2 := sq_pos_of_pos heps
  have hL5 : Real.log z ≤ (Real.log z)^5 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hL : 1 ≤ (Real.log z)^4) hL0.le
    nlinarith
  have hpay : 8*C ≤ (Real.log z)^5*(eta*eps^2) := by
    have hh := (div_le_iff₀ (mul_pos heta he2)).mp ((le_max_right _ _).trans hzL)
    exact hh.trans (mul_le_mul_of_nonneg_right hL5 (mul_pos heta he2).le)
  have hfirst : 4*C/(eta*(Real.log z)^5) ≤ eps^2/2 := by
    apply (div_le_iff₀ (by positivity : 0 < eta*(Real.log z)^5)).mpr
    nlinarith
  have hpower : 0 < z^((92 : ℝ)/100) := Real.rpow_pos_of_pos hz0 _
  have hsecond : 1/z^((92 : ℝ)/100) ≤ eps^2/2 := by
    apply (div_le_iff₀ hpower).mpr
    have hh := (div_le_iff₀ he2).mp hzpow
    nlinarith
  refine ⟨hz,hL,?_⟩
  intro R N n hR hRz hN hcount
  apply (collision_error_bound z R N n eta C hz hR hRz hN heta hC hL hcount).trans
  linarith

end ErdosSourceCollision

end

end Erdos970

end OAI
