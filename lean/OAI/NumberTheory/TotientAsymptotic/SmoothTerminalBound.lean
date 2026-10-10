import OAI.NumberTheory.TotientAsymptotic.SmoothTerminalMass
import OAI.NumberTheory.TotientAsymptotic.MertensProduct

namespace OAI

/-! The single-surviving-prime terminal sum, with the two logarithms retained. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem smooth_terminal_log_bound : ∃ C : ℝ,0 < C ∧
    ∀ d N : ℕ,0 < d → 2 ≤ N → ∀ Q : Finset SmoothTerminalTriple,
    (∀ z ∈ Q,TerminalConditions d N z) →
    (∑ z ∈ Q,(terminalFirst z:ℝ)⁻¹) ≤
      C*(2:ℝ)^d.primeFactorsList.length*(Real.log N)^2 := by
  obtain ⟨C,hC,hm⟩ := mertensProductInput
  refine ⟨C^2,by positivity,?_⟩
  intro d N hd hN Q hQ
  have hE : 0 ≤ primeEulerProduct N := by
    have hh := smooth_residual_reciprocal_mass N (∅:Finset ℕ) (by simp)
    simpa using hh
  have hpow := pow_le_pow_left₀ hE (hm N hN) 2
  have hh := (smooth_terminal_mass d N hd Q hQ).trans
    (mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ 2^d.primeFactorsList.length))
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
