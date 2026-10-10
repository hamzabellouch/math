import OAI.NumberTheory.JointDickman.Counting.CoefficientWeights
import OAI.NumberTheory.JointDickman.Amplification.WeightedPartialSummation
import OAI.NumberTheory.JointDickman.Arithmetic.RoughHarmonicLaw

namespace OAI

/-! # Smooth real tests of the coefficient progression law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

open Classical in
theorem finiteCountingFunction_coefficient_residue {q : ℕ}
    (B : ℕ) (r : ZMod q) (Y : ℝ) :
    finiteCountingFunction (fun n => if (n : ZMod q) = r then coefficientWeight B n else 0) Y =
      progressionSum (Ioc 0 ⌊Y⌋₊) (coefficientWeight B) r := by
  unfold finiteCountingFunction progressionSum
  rw [← Ioc_insert_left (Nat.zero_le ⌊Y⌋₊), sum_insert left_notMem_Ioc]
  simp [coefficientWeight]

open Classical in
/-- Weighted equidistribution in one unit class. The constants and
expansion order are independent of the smooth test. -/
theorem coefficientProgression_smooth_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) → ∀ r : (ZMod q)ˣ,
      ∀ φ φ' : ℝ → ℝ, ∀ M N : ℝ, 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, |φ t| ≤ M) → (∀ t ∈ Set.Icc a b, |φ' t| ≤ N) →
      |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then φ n * coefficientWeight B n else 0) -
        (∫ t in a..b, φ t * coefficientDensity c H B (Real.log t / B)) / q.totient| ≤
        K * (B : ℝ) ^ (-D) * b * (2 * M + N * (b - a)) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficientProgression_expansion hSD hSW hM hD
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hloga q _ hq r φ φ' M N hM0 hN hφ hφ' hvalue hderiv
  let w : ℕ → ℝ := fun n => if (n : ZMod q) = r then coefficientWeight B n else 0
  let F : ℝ → ℝ := fun t => coefficientModel c H B t / q.totient
  let F' : ℝ → ℝ := fun t => coefficientDensity c H B (Real.log t / B) / q.totient
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (F' t) t :=
    (hasDerivAt_coefficientModel c H B hB (by linarith [ht.1])).div_const _
  have hFc : ContinuousOn F (Set.Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hF'c : ContinuousOn F' (Set.Icc a b) := by
    have heq : F' = fun t => coefficientScale B *
        roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H (Real.log t) / q.totient := by
      funext t
      simp only [F', coefficientDensity, mul_div_cancel₀ _ hB0]
    rw [heq]
    intro t ht
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact ((continuousAt_const.mul ((roughDensityPolynomial_continuousAt c _ _ H hlogt).comp
      (Real.continuousAt_log (by linarith [ht.1] : t ≠ 0)))).div_const _).continuousWithinAt
  have he : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤
      (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt := hloga.trans (Real.log_le_log (by linarith : 0 < a) ht.1)
    simpa only [w, F, finiteCountingFunction_coefficient_residue, mul_right_comm] using
      hboundB t hlogt (ha.trans ht.1) q hq r
  have htest := weighted_counting_error_le w F φ φ' (by linarith) hab
    (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg B) _)) hM0 hN hφ hφ' hFc hvalue hderiv he
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hφ t (Set.uIcc_of_le hab ▸ ht))
    (fun t ht => hd t (Set.uIcc_of_le hab ▸ ht))
    (hφ'.intervalIntegrable_of_Icc hab) (hF'c.intervalIntegrable_of_Icc hab)
  rw [← hparts] at htest
  have hsum : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * w n) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then φ n * coefficientWeight B n else 0 := by
    apply sum_congr rfl
    intro n _
    simp only [w, mul_ite, mul_zero]
  rw [hsum] at htest
  have hint : (∫ t in a..b, φ t * F' t) =
      (∫ t in a..b, φ t * coefficientDensity c H B (Real.log t / B)) / q.totient := by
    simp only [F', ← mul_div_assoc, intervalIntegral.integral_div]
  rw [hint] at htest
  exact htest

end JointDickman

end OAI
