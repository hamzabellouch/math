import Mathlib

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem eventually_const_rpow_le {a b : ℝ} (hab : a<b) (A : ℝ) {B : ℝ} (hB : 0<B) :
    ∀ᶠ n : ℕ in atTop,A*(n:ℝ)^a ≤ B*(n:ℝ)^b := by
  have H := ((tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul A
  have H0 : Tendsto (fun n : ℕ => A*(n:ℝ)^(a-b)) atTop (𝓝 0) := by
    simpa only [neg_sub,mul_zero,Function.comp_apply] using H
  filter_upwards [H0.eventually_le_const hB,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  rw [Real.rpow_sub hp] at hn
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hp b)).mp (by simpa only [mul_div_assoc] using hn)

theorem polynomial_rpow_exp_decay {u c : ℝ} (hu : 0<u) (hc : 0<c) (d : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^d*Real.exp (-c*(n:ℝ)^u)) atTop (𝓝 0) := by
  have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d:ℝ)/u) c hc).comp
    ((tendsto_rpow_atTop hu).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hp.le,mul_div_cancel₀ _ (ne_of_gt hu),Real.rpow_natCast]

theorem eventual_polynomial_stretched_tail {t u c ε : ℝ} (htu : t<u) (hu : 0<u)
    (hc : 0<c) (hε : 0<ε) (K : ℝ) (hK : 0≤K) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop,K*((n:ℝ)+1)^d*Real.exp (-c*(n:ℝ)^u) ≤ ε*Real.exp (-(n:ℝ)^t) := by
  have H := (polynomial_rpow_exp_decay hu (half_pos hc) d).const_mul (K*2^d)
  have H0 : Tendsto (fun n : ℕ => (K*2^d)*((n:ℝ)^d*Real.exp (-(c/2)*(n:ℝ)^u))) atTop (𝓝 0) := by
    simpa only [mul_zero] using H
  filter_upwards [eventually_const_rpow_le htu 1 (half_pos hc),
    H0.eventually_le_const hε,eventually_ge_atTop (1:ℕ)] with n hn hsmall hn1
  have hnp : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hn1' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpow : ((n:ℝ)+1)^d≤2^d*(n:ℝ)^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hfactor : K*((n:ℝ)+1)^d*Real.exp (-(c/2)*(n:ℝ)^u) ≤ ε :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) (Real.exp_pos _).le).trans
      (by nlinarith only [hsmall])
  have he : Real.exp (-(c/2)*(n:ℝ)^u)≤Real.exp (-(n:ℝ)^t) := by
    apply Real.exp_le_exp.mpr
    linarith only [hn]
  calc
    _ = (K*((n:ℝ)+1)^d*Real.exp (-(c/2)*(n:ℝ)^u))*Real.exp (-(c/2)*(n:ℝ)^u) := by
      rw [mul_assoc (K*((n:ℝ)+1)^d),← Real.exp_add]
      congr 2
      ring
    _ ≤ ε*Real.exp (-(n:ℝ)^t) := mul_le_mul hfactor he (Real.exp_pos _).le hε.le

end SK.Analytic

end
end

end OAI
