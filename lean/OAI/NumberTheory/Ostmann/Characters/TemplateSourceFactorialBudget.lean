import Mathlib.Analysis.Complex.ExponentialBounds
import OAI.NumberTheory.Ostmann.Characters.FactorialContradictionThreshold
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Filter InitialCharacterScale

theorem exists_sourceFactorial_threshold (B BD β : ℝ) :
    ∃N : ℕ,∀n : ℕ,N≤n → ∀α τ : ℝ,0<α → 0<τ →
      ∀ᶠ L : ℝ in atTop,
        2*Real.exp ((BD+20*Real.log (depthScale (n+1))+1)*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ))*
          (Real.exp ((2*β+3)*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ))/
            (factorialCount n (wordSize (n+1) L):ℝ)+Real.exp (-(τ/2)*Real.exp (α*L))) <
          Real.exp (-2*B*(2:ℝ)^(n+1)*(wordSize (n+1) L:ℝ)) := by
  have hε : 60*(1/10000:ℝ)<Real.log 2 := by linarith [Real.log_two_gt_d9]
  obtain ⟨N,hN⟩ := exists_factorial_depth_threshold B (BD+1) (2*β+3) (1/10000) hε
  refine ⟨N,?_⟩
  intro n hn α τ hα hτ
  have ht := factorial_comparison_eventually_lt n B
    (BD+1+60*(1/10000:ℝ)*(n+1)) (2*β+3) 1
    (depthScale_pos (n+1)) (half_pos hτ) hα (hN n hn)
  have hv : BD+20*Real.log (depthScale (n+1))+1 = BD+1+60*(1/10000:ℝ)*(n+1) := by
    rw [depthScale,Real.log_exp,Nat.cast_add,Nat.cast_one]
    ring
  filter_upwards [ht] with L hL
  rw [hv]
  simpa only [wordSize,factorialBulk,factorialMass,one_mul,mul_assoc] using hL

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
