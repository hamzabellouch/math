import OAI.NumberTheory.JointDickman.Counting.PeriodicCoefficientLaw
import OAI.NumberTheory.JointDickman.Amplification.ScaledOscillatoryTests
import OAI.NumberTheory.JointDickman.Amplification.OscillatoryError

namespace OAI

/-! # The scaled coefficient law with explicit oscillatory savings -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

open Classical in
/-- The analytic estimate in equation (1), before evaluating the finite
unit-phase sum. The expansion order is independent of the smooth test. -/
theorem coefficient_scaled_oscillatory_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b X : ℝ, 0 < a → a ≤ b → 0 < X → 9 ≤ a * X →
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (15 : ℝ) →
      ∀ ψ : ZMod q → ℂ, (∀ r : (ZMod q)ˣ, ‖ψ r‖ ≤ 1) →
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) → |ξ| ≤ (B : ℝ) ^ (14 : ℝ) →
      ‖(∑ n ∈ Ioc ⌊a * X⌋₊ ⌊b * X⌋₊, ψ (n : ZMod q) *
          (scaledOscillatoryTest w ξ X n * (coefficientWeight B n : ℂ))) -
        (X : ℂ) * ((∑ r : (ZMod q)ˣ, ψ r) / (q.totient : ℂ)) *
          ∫ s in a..b, oscillatoryTest w ξ s *
            (coefficientDensity c H B (Real.log (s * X) / B) : ℂ)‖ ≤
        (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X * (B : ℝ) ^ (-50 : ℝ) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ :=
    coefficient_periodic_smooth_test hSD hSW hM (D := 79) (by norm_num)
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro a b X ha hab hX haX hloga q _ hq ψ hψ w w' M N ξ hM0 hN hw hw' hwbound hw'bound hξ
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hq100 : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) :=
    hq.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num))
  have hcw : Continuous w := continuous_iff_continuousAt.mpr (fun t => (hw t).continuousAt)
  have htest := hboundB (a * X) (b * X) haX
    (mul_le_mul_of_nonneg_right hab hX.le) hloga q hq100 ψ hψ
    (scaledOscillatoryTest w ξ X) (scaledOscillatoryTestDeriv w w' ξ X)
    M ((N + 2 * Real.pi * |ξ| * M) / X) hM0 (by positivity)
    (fun t _ => hasDerivAt_scaledOscillatoryTest (hw (t / X)))
    (scaledOscillatoryTestDeriv_continuous hcw hw' ξ X).continuousOn
    (fun t _ => scaledOscillatoryTest_norm_le (hwbound (t / X)))
    (fun t _ => scaledOscillatoryTestDeriv_norm_le hX (hwbound (t / X)) (hw'bound (t / X)))
  have hint := scaledOscillatoryTest_integral w
    (fun t => (coefficientDensity c H B (Real.log t / B) : ℂ)) ξ a b X hX.ne'
  rw [hint] at htest
  have hmain : (∑ r : (ZMod q)ˣ, ψ r) *
        ((X : ℂ) * (∫ s in a..b, oscillatoryTest w ξ s *
            (coefficientDensity c H B (Real.log (s * X) / B) : ℂ)) / (q.totient : ℂ)) =
      (X : ℂ) * ((∑ r : (ZMod q)ˣ, ψ r) / (q.totient : ℂ)) *
        ∫ s in a..b, oscillatoryTest w ξ s *
          (coefficientDensity c H B (Real.log (s * X) / B) : ℂ) := by ring
  rw [hmain] at htest
  exact htest.trans (oscillatory_error_bookkeeping hB1 hq hK hX
    (ha.le.trans hab) hab hM0 hN hξ)

end JointDickman

end OAI
