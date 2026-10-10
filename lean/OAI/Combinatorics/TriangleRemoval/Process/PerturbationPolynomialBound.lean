import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
open Filter
open scoped BigOperators

lemma perturbation_polynomial_bound (T : ℝ) (hT : 0 ≤ T) (K : ℕ) :
    (∑ j ∈ Finset.range K, ((1+2*T)*6*T)^j*(1+2*T)) ≤
      (2*(K : ℝ)*12^K)*(1+T)^(2*K+1) := by
  have hH : 1 ≤ 1+T := by linarith
  have hb : (1+2*T)*6*T ≤ 12*(1+T)^2 := by nlinarith
  have hb1 : 1 ≤ (12 : ℝ)*(1+T)^2 := by nlinarith [sq_nonneg T]
  have hsum := Finset.sum_le_card_nsmul (Finset.range K)
    (fun j => ((1+2*T)*6*T)^j*(1+2*T)) ((12*(1+T)^2)^K*(2*(1+T))) (by
      intro j hj
      have hjK : j ≤ K := (Finset.mem_range.mp hj).le
      have hp := (pow_le_pow_left₀ (by positivity) hb j).trans (pow_le_pow_right₀ hb1 hjK)
      exact mul_le_mul hp (by linarith) (by positivity) (by positivity))
  simp only [Finset.card_range,nsmul_eq_mul] at hsum
  refine hsum.trans_eq ?_
  rw [mul_pow,← pow_mul,pow_add,pow_one]
  ring

lemma spectral_remainder_eventual {γ : ℝ} (hγ : 0 < γ) (K : ℕ)
    (hK : 4/γ ≤ (K : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, 0 ≤ ε → ε ≤ (n : ℝ)^(-γ) →
      (n : ℝ)*((ε*Real.log n)^K * Real.exp (Real.log n*ε)) ≤ 1 := by
  have hγ2 : 0 < γ/2 := by positivity
  have hlog := ((isLittleO_log_rpow_atTop hγ2).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound zero_lt_one
  have hnexp : ∀ᶠ n : ℕ in atTop, Real.exp 1 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [hlog,hnexp,eventually_ge_atTop (1 : ℕ)] with n hl hnE hn ε hε hεn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hl' : Real.log n ≤ (n : ℝ)^(γ/2) := by
    simpa only [Function.comp_apply,one_mul,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hn0.le _)] using hl
  have hεlog : ε*Real.log n ≤ (n : ℝ)^(-(γ/2)) := by
    calc
      _ ≤ (n : ℝ)^(-γ)*(n : ℝ)^(γ/2) :=
        mul_le_mul hεn hl' hlog0 (by positivity)
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  have hεlog1 : Real.log n*ε ≤ 1 := by
    rw [mul_comm]
    exact hεlog.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
  have hpower : (ε*Real.log n)^K ≤ (n : ℝ)^(-(2 : ℝ)) := by
    have hKg : 4 ≤ (K : ℝ)*γ := (div_le_iff₀ hγ).mp hK
    calc
      _ ≤ ((n : ℝ)^(-(γ/2)))^K := pow_le_pow_left₀ (by positivity) hεlog _
      _ = (n : ℝ)^(-(γ/2)*(K : ℝ)) := by rw [Real.rpow_mul hn0.le,Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  calc
    _ ≤ (n : ℝ)*((n : ℝ)^(-(2 : ℝ))*Real.exp 1) := by
      gcongr
    _ = (n : ℝ)⁻¹*Real.exp 1 := by
      have hh : (n : ℝ)*(n : ℝ)^(-(2 : ℝ)) = (n : ℝ)⁻¹ := by
        conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hn0]
        norm_num [Real.rpow_neg_one]
      rw [← mul_assoc,hh]
    _ ≤ (n : ℝ)⁻¹*(n : ℝ) := mul_le_mul_of_nonneg_left hnE (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0.ne'

end SharpTerminalLeave

end

end OAI
