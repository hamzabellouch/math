import OAI.NumberTheory.JointDickman.Arithmetic.RoughCountTruncation

namespace OAI

/-! # A fixed divisor changes logarithmic frequency windows negligibly -/
namespace JointDickman
open Filter
open scoped Topology

lemma fixed_divisor_logarithmic_window {d : ℕ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N/d ∧
      3*(Real.log (N:ℝ))^8 ≤ 4*(Real.log (N/d:ℕ))^8 := by
  have hdiv := Nat.tendsto_div_const_atTop hd.ne'
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hdiv)
  filter_upwards [hdiv.eventually (eventually_ge_atTop 1),
    hlog.eventually (eventually_ge_atTop (31*Real.log (2*d:ℝ)))] with N hk hlogk
  refine ⟨hk,?_⟩
  change 31*Real.log (2*d:ℝ) ≤ Real.log (N/d:ℕ) at hlogk
  have hN1 : 1 ≤ N := hk.trans (Nat.div_le_self N d)
  have hkr : 0 < (N/d:ℕ) := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hbound : (N:ℝ) ≤ (2*d:ℝ)*(N/d:ℕ) := by
    have he := Nat.div_add_mod N d
    have hm := Nat.mod_lt N hd
    have hs : N ≤ 2*d*(N/d) := by nlinarith
    exact_mod_cast hs
  have hlogN : Real.log (N:ℝ) ≤ (32/31:ℝ)*Real.log (N/d:ℕ) := by
    have hh := Real.log_le_log hNr hbound
    rw [Real.log_mul (by positivity : (2*d:ℝ)≠0) (by exact_mod_cast hkr.ne')] at hh
    linarith
  have hnlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hklog : 0 ≤ Real.log (N/d:ℕ) := Real.log_nonneg (by exact_mod_cast hk)
  have hp := pow_le_pow_left₀ hnlog hlogN 8
  rw [mul_pow] at hp
  have hnum : 3*(32/31:ℝ)^8 ≤ 4 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hnum (pow_nonneg hklog 8)
  nlinarith

end JointDickman

end OAI
