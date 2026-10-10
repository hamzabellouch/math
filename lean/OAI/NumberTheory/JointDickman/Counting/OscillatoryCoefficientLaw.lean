import OAI.NumberTheory.JointDickman.Counting.ScaledCoefficientLaw
import OAI.NumberTheory.JointDickman.Counting.CoefficientWindow
import OAI.NumberTheory.JointDickman.Amplification.AdditivePhaseBridge
import OAI.NumberTheory.JointDickman.Amplification.CompactOscillatorySupport

namespace OAI

/-! # Manuscript equation (1): the oscillatory coefficient law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

noncomputable def coefficientExponentialSum (B q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (ξ X : ℝ) (w : ℝ → ℝ) : ℂ :=
  ∑' n : ℕ, (coefficientWeight B n : ℂ) * (w (n / X) : ℂ) *
    additivePhase (((u : ZMod q).val : ℝ) * n / q + ξ * n / X)

open Classical in
/-- Equation (1) follows from the three cited arithmetic inputs. The
expansion is fixed before the test and its support are chosen. -/
theorem coefficient_oscillatory_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9 / 10 : ℝ) * B) ((11 / 5 : ℝ) * B) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (15 : ℝ) → ∀ u : (ZMod q)ˣ,
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) → |ξ| ≤ (B : ℝ) ^ (14 : ℝ) →
      ‖coefficientExponentialSum B q u ξ X w -
        (X : ℂ) * ((μ q : ℂ) / (q.totient : ℂ)) *
          ∫ s : ℝ, (w s : ℂ) * (coefficientDensity c H B (Real.log (s * X) / B) : ℂ) *
            additivePhase (ξ * s)‖ ≤
        (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X * (B : ℝ) ^ (-50 : ℝ) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficient_scaled_oscillatory_test hSD hSW hM
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  intro a b ha hab
  filter_upwards [hbound, coefficient_support_window ha] with B hboundB hwindow
  intro X hX hlogX q _ hq u w w' M N ξ hM0 hN hw hw' hwbound hw'bound hsupport hξ
  obtain ⟨haX, hloga⟩ := hwindow X hX hlogX.1
  have htest := hboundB a b X ha hab hX haX hloga q hq
    (fun r => ZMod.stdAddChar ((u : ZMod q) * r))
    (fun r => (norm_stdAddChar _).le) w w' M N ξ hM0 hN hw hw' hwbound hw'bound hξ
  rw [ramanujan_sum_unit_frequency u] at htest
  have hsum := tsum_eq_Ioc_of_scaled_support ha.le hab hX hsupport
    (fun n => ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) *
      (scaledOscillatoryTest w ξ X n * (coefficientWeight B n : ℂ)))
    (fun n hn => by simp only [scaledOscillatoryTest, oscillatoryTest, hn,
      Complex.ofReal_zero, zero_mul, mul_zero])
  rw [← hsum, oscillatory_integral_eq_integral hab hsupport] at htest
  have heq : (∑' n : ℕ, ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) *
      (scaledOscillatoryTest w ξ X n * (coefficientWeight B n : ℂ))) =
      coefficientExponentialSum B q u ξ X w := by
    unfold coefficientExponentialSum
    apply tsum_congr
    intro n
    rw [scaledOscillatoryTest, oscillatoryTest, unit_nat_phase, additivePhase_add]
    have ht : ξ * ((n : ℝ) / X) = ξ * n / X := by ring
    rw [ht]
    ring
  rw [heq] at htest
  have hint : (∫ s : ℝ, oscillatoryTest w ξ s *
      (coefficientDensity c H B (Real.log (s * X) / B) : ℂ)) =
      ∫ s : ℝ, (w s : ℂ) * (coefficientDensity c H B (Real.log (s * X) / B) : ℂ) *
        additivePhase (ξ * s) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by unfold oscillatoryTest; ring)
  rw [hint] at htest
  exact htest

end JointDickman

end OAI
