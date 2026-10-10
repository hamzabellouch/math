import Mathlib
import OAI.Combinatorics.SharpRamsey.Bounds.Lower

namespace OAI

/-! Two-sided Ramsey bounds and the logarithmic limit from a prime-field construction. -/

section
namespace SharpLogRamsey

theorem mainLimit_of_mainBounds (s : ℕ) (h : MainBounds s) : MainLimit s := by
  obtain ⟨C,hC,h⟩ := h
  have hlog : Filter.Tendsto (fun t : ℕ => Real.log (t:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto (fun t : ℕ => Real.log (Real.log (t:ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨t₀,ht₀⟩ := h (ε/2) (by positivity)
  obtain ⟨t₁,ht₁⟩ := Filter.eventually_atTop.mp
    (hloglog.eventually (Filter.eventually_gt_atTop (max 0 (2*|Real.log C|/ε))))
  refine ⟨max (max t₀ t₁) 2, fun t ht => ?_⟩
  have htl : t₀≤t := (le_max_left t₀ t₁).trans ((le_max_left _ _).trans ht)
  have htll : t₁≤t := (le_max_right t₀ t₁).trans ((le_max_left _ _).trans ht)
  have ht2 : 2≤t := (le_max_right _ _).trans ht
  have htp : (0:ℝ)<t := by exact_mod_cast (by omega : 0<t)
  have hlt : 0<Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<t))
  have hll0 : 0<Real.log (Real.log (t:ℝ)) := (le_max_left _ _).trans_lt (ht₁ t htll)
  have hllbig : 2*|Real.log C|/ε<Real.log (Real.log (t:ℝ)) :=
    (le_max_right _ _).trans_lt (ht₁ t htll)
  obtain ⟨hl,hu⟩ := ht₀ t htl
  have hp : 0<(t:ℝ)^(s-1)/Real.rpow (Real.log (t:ℝ)) ((s-2:ℕ)+(ε/2)) :=
    div_pos (pow_pos htp _) (Real.rpow_pos_of_pos hlt _)
  have hr : 0<(ramsey s t:ℝ) := hp.trans_le hl
  have hl' := Real.log_le_log hp hl
  change Real.log ((t:ℝ)^(s-1)/(Real.log (t:ℝ))^(((s-2:ℕ):ℝ)+ε/2)) ≤ Real.log (ramsey s t:ℝ) at hl'
  rw [Real.log_div (pow_ne_zero (s-1) (ne_of_gt htp))
    (ne_of_gt (Real.rpow_pos_of_pos hlt (((s-2:ℕ):ℝ)+(ε/2)))), Real.log_pow,Real.log_rpow hlt] at hl'
  have hu' := Real.log_le_log hr hu
  rw [Real.log_div (mul_ne_zero (ne_of_gt hC) (pow_ne_zero (s-1) (ne_of_gt htp)))
    (pow_ne_zero (s-2) (ne_of_gt hlt)), Real.log_mul (ne_of_gt hC)
      (pow_ne_zero (s-1) (ne_of_gt htp)),Real.log_pow,Real.log_pow] at hu'
  have herr : |Real.log C| < (ε/2)*Real.log (Real.log (t:ℝ)) := by
    have he := (div_lt_iff₀ hε).mp hllbig
    nlinarith
  have hlow : ((s-2:ℕ):ℝ)-ε/2 <
    (((s-1:ℕ):ℝ)*Real.log (t:ℝ)-Real.log (ramsey s t:ℝ))/
      Real.log (Real.log (t:ℝ)) := by
    apply (lt_div_iff₀ hll0).mpr
    have habs := le_abs_self (Real.log C)
    nlinarith
  have hupp : (((s-1:ℕ):ℝ)*Real.log (t:ℝ)-Real.log (ramsey s t:ℝ))/
      Real.log (Real.log (t:ℝ)) ≤ ((s-2:ℕ):ℝ)+ε/2 := by
    apply (div_le_iff₀ hll0).mpr
    nlinarith
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith
end SharpLogRamsey

namespace SharpLogRamsey

theorem main_of_primeConstruction (s : ℕ) (hs : 6 ≤ s)
    (hprime : LowerTransfer.PrimeConstruction (s-1)) : MainBounds s ∧ MainLimit s := by
  have hb : MainBounds s := by
    obtain ⟨C,hC,t₀,ht₀⟩ := Upper.ramsey_upper (by omega : 3 ≤ s)
    refine ⟨C,hC,fun ε hε => ?_⟩
    have hl := LowerTransfer.all_epsilon_lower (s-1) (by omega) hprime ε hε
    have he : s-1+1=s := by omega
    have he' : s-1-1=s-2 := by omega
    rw [he,he'] at hl
    obtain ⟨t₁,ht₁⟩ := Filter.eventually_atTop.mp hl
    exact ⟨max t₀ t₁,fun t ht => ⟨ht₁ t ((le_max_right _ _).trans ht),
      ht₀ t ((le_max_left _ _).trans ht)⟩⟩
  exact ⟨hb,mainLimit_of_mainBounds s hb⟩
end SharpLogRamsey

end

end OAI
