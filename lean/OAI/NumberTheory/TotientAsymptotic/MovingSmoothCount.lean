import OAI.NumberTheory.TotientAsymptotic.MovingSmoothDecay
import OAI.NumberTheory.TotientAsymptotic.MertensProduct

namespace OAI

/-! Distinct totients with a very smooth preimage have a summable counting bound. -/
noncomputable section
namespace TotientAsymptotic

theorem moving_smooth_totient_count : ∃ C : ℝ,0 < C ∧ ∀ x : ℝ,
    Real.exp (Real.exp 1) ≤ x → 10000 ≤ B x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ (v:ℝ) ≤ x ∧
      largestPrimeFactor n ≤ movingSmoothCutoff x) →
    (Q.card:ℝ) ≤ C*x/(Real.log x)^3 := by
  obtain ⟨A,hA,hpreimage⟩ := preimage_loglog_bound
  obtain ⟨D,hD,hmertens⟩ := mertensProductInput
  refine ⟨1+A*D^4,by positivity,?_⟩
  intro x hx hB Q hQ
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le hx
  have hx0 : 0 < x := by linarith only [hx1]
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hb : 0 ≤ B x := by linarith only [hB]
  let K := movingSmoothCutoff x
  let N := ⌊A*x*B x⌋₊
  have hk := moving_smooth_budget hx1 hB
  have hcount := smooth_totient_count_of_preimage (K:=K) (N:=N) hk.1 (Real.log x/2) Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvx,hsmooth⟩ := hQ v hv
    refine ⟨n,hn,hφ,?_,hsmooth⟩
    apply Nat.le_floor
    exact hpreimage x hx n hn (by rwa [hφ]))
  have hN : (N:ℝ) ≤ A*x*B x := Nat.floor_le (by positivity)
  have heuler : (primeEulerProduct K)^4 ≤ D^4*(Real.log x)^4 := by
    have hh := (hmertens K hk.1).trans
      (mul_le_mul_of_nonneg_left hk.2.2.1 hD.le)
    have hp := pow_le_pow_left₀ (primeEulerProduct_pos K).le hh 4
    simpa only [mul_pow] using hp
  have hrankin := moving_smooth_rankin_factor hx1 hB
  have htail : (N:ℝ)*Real.exp (-(Real.log x/2)/(4*Real.log K))*(primeEulerProduct K)^4 ≤
      A*D^4*x/(Real.log x)^3 := by
    calc
      _ ≤ (A*x*B x)*Real.exp (-60*B x)*(D^4*(Real.log x)^4) := by
        exact mul_le_mul (mul_le_mul hN hrankin (Real.exp_pos _).le (by positivity))
          heuler (by positivity) (by positivity)
      _ = (A*D^4*x)*(B x*Real.exp (-60*B x)*(Real.exp (B x))^4) := by
        rw [B,Real.exp_log hl]
        ring
      _ ≤ (A*D^4*x)*Real.exp (-3*B x) :=
        mul_le_mul_of_nonneg_left (moving_smooth_decay hb) (by positivity)
      _ = _ := by rw [exp_neg_triple_B hx1]; ring
  have hsmall := moving_smooth_small_part hx1 hB
  apply hcount.trans
  change Real.exp (Real.log x/2)+(N:ℝ)*Real.exp (-(Real.log x/2)/(4*Real.log K))*
    (primeEulerProduct K)^4 ≤ _
  have hh := add_le_add hsmall htail
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
