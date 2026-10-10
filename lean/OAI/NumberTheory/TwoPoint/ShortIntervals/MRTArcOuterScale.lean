import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcQuotientScale

namespace OAI

/-! Uniform outer logarithms at the final modulus exponent. The proof
keeps the actual floor quotient and allows the combined divisor W^6. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_polylog_quotient_logs {X c : ℕ} (hX : 2 ≤ X)
    (hscale : (Real.log (X:ℝ))^2 ≤ (X:ℝ))
    (hc : 0 < c) (hcL : (c:ℝ) ≤ Real.log (X:ℝ)) :
    Real.log (X:ℝ)/2 ≤ Real.log (X/c+1:ℕ) ∧
      Real.log (X/c+1:ℕ) ≤ 2*Real.log (X:ℝ) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hc0 : 0 < (c:ℝ) := by exact_mod_cast hc
  have hcX : (c:ℝ)^2 ≤ X := (pow_le_pow_left₀ hc0.le hcL 2).trans hscale
  have hlogc := Real.log_le_log (pow_pos hc0 2) hcX
  rw [Real.log_pow] at hlogc
  norm_num only [Nat.cast_ofNat] at hlogc
  have hquot : (X:ℝ)/c < (X/c+1:ℕ) := by
    apply (div_lt_iff₀ hc0).mpr
    have hh : (X:ℝ) < (c:ℝ)*(X/c+1:ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ X hc
    simpa only [mul_comm] using hh
  have hlo := Real.log_le_log (div_pos hX0 hc0) hquot.le
  rw [Real.log_div hX0.ne' hc0.ne'] at hlo
  have hq0 : (0:ℝ) < (X/c+1:ℕ) := by positivity
  have hqX : ((X/c+1:ℕ):ℝ) ≤ (X:ℝ)^2 := by
    have hh : ((X/c+1:ℕ):ℝ) ≤ (X:ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.div_le_self X c) 1
    have hX2 : (2:ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hhi := Real.log_le_log hq0 hqX
  rw [Real.log_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hhi
  exact ⟨by linarith,hhi⟩

theorem mrt_arc_quotient_outer_logs_sharp :
    ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (X:ℝ) ∧
      ∀ W : ℝ, 1 ≤ W → W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ c : ℕ, 0 < c → (c:ℝ) ≤ W^6 →
        Real.log (X:ℝ)/2 ≤ Real.log (X/c+1:ℕ) ∧
        Real.log (X/c+1:ℕ) ≤ 2*Real.log (X:ℝ) := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show (0:ℝ)<1 by norm_num)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    hlog.eventually (eventually_ge_atTop (2:ℝ)),eventually_ge_atTop (2:ℕ)]
    with X hsmall hL hX
  dsimp only [id] at hsmall
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log (X:ℝ))),
    Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg X : (0:ℝ)≤X),one_mul] at hsmall
  refine ⟨hL,?_⟩
  intro W hW hWX c hc hcW
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hp : W^6 ≤ (Real.log (X:ℝ))^(6/125:ℝ) := by
    calc
      _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^6 :=
        pow_le_pow_left₀ (by linarith) hWX 6
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
        norm_num
  have hcL : (c:ℝ) ≤ Real.log (X:ℝ) := by
    apply hcW.trans (hp.trans _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ Real.log (X:ℝ) by linarith) (show (6/125:ℝ)≤1 by norm_num)
  exact mrt_polylog_quotient_logs hX hsmall hc hcL

end TwoPointCorrelations

end OAI
