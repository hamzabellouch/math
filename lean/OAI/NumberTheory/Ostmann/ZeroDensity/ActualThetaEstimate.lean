import OAI.NumberTheory.Ostmann.ZeroDensity.ResiduePsiEstimate
import OAI.NumberTheory.Ostmann.ZeroDensity.ResiduePrimePowerRemoval
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveRieszErrorDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualProgressionInput

namespace OAI

/-! # The actual prime-progression estimate, with no analytic input hypotheses -/

namespace Ostmann

open Filter

theorem actual_theta_eventual_bound : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, a.Coprime q →
      |primeProgressionTheta q a X - thetaMainTerm q.totient
        (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          C * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := residuePsi_eventual_bound
  refine ⟨c, C + 1, hc, by positivity, ?_⟩
  filter_upwards [hbound, primitive_riesz_error_decay c hc,
    eventually_ge_atTop (1 : ℝ)] with X hmain herr hX
  intro q hq a ha
  have hp := residuePsi_prime_error q a X hX
  have he := herr 0 (by simpa using (Real.exp_nonneg (Real.sqrt (Real.log X))))
  norm_num only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at he
  have hs : 0 ≤ Real.sqrt X * Real.log X :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hX)
  have htri := abs_sub_le (primeProgressionTheta q a X) (residuePsi q a X)
    (thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X)
  rw [abs_sub_comm (primeProgressionTheta q a X) (residuePsi q a X)] at htri
  have hm := hmain q hq a ha
  nlinarith

theorem actual_theta_bounded_range : ∃ D : ℝ, 0 < D ∧
    ∀ (q a : ℕ) (X L : ℝ), 1 ≤ q → 1 ≤ X → X ≤ L →
      |primeProgressionTheta q a X - thetaMainTerm q.totient
        (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          (2 * Real.log L + D) * X := by
  obtain ⟨D, hD, hmain⟩ := canonical_theta_sqrt_bound
  refine ⟨D, hD, ?_⟩
  intro q a X L hq hX hXL
  have hXp : 0 ≤ X := by linarith
  have hqp : 0 < q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hroot : 1 ≤ Real.sqrt q := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hqR)
  have hm := (hmain q a X hqp hX).trans
    (div_le_self (show 0 ≤ D * X by positivity) hroot)
  have hcount := residuePsi_counting_bound q a X hqp hX
  have hlog : Real.log X ≤ Real.log L := Real.log_le_log (by linarith) hXL
  have hdiv : X / q ≤ X := div_le_self hXp hqR
  have hb : residuePsi q a X ≤ 2 * X * Real.log L := by
    calc
      _ ≤ (X / q + 1) * Real.log X := hcount
      _ ≤ (2 * X) * Real.log L := mul_le_mul (by linarith) hlog
        (Real.log_nonneg hX) (by positivity)
  have hp := primeProgressionTheta_bounds q a X
  have ht := abs_sub (primeProgressionTheta q a X)
    (thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X)
  rw [abs_of_nonneg hp.1] at ht
  nlinarith

/-- Montgomery--Vaughan's progression estimate specialized to the canonical,
actually constructed exceptional zero. All inputs have been discharged. -/
theorem actualProgressionTheta : ActualProgressionTheta := by
  obtain ⟨c, C, hc, hC, hbound⟩ := actual_theta_eventual_bound
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hbound
  obtain ⟨D, hD, hsmall⟩ := actual_theta_bounded_range
  let L := max 2 X0
  let K := 2 * Real.log L + D
  let B := C + K * Real.exp (c * Real.sqrt (Real.log L))
  have hL : 2 ≤ L := le_max_left _ _
  have hK : 0 ≤ K := by
    have hl : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    dsimp [K]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨c, B, hc, hB, ?_⟩
  intro q hq a ha X hX
  have hXp : 0 ≤ X := by linarith
  by_cases hlarge : X0 ≤ X
  · exact (hX0 X hlarge q hq a ha).trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hXp
      exact le_add_of_nonneg_right (mul_nonneg hK (Real.exp_nonneg _)))
  · have hXL : X ≤ L := (le_of_not_ge hlarge).trans (le_max_right _ _)
    have hsmall' := hsmall q a X L hq (by linarith) hXL
    have hy : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log L) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hXL)
    have he : 1 ≤ Real.exp (c * Real.sqrt (Real.log L)) *
        Real.exp (-c * Real.sqrt (Real.log X)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hrate : K ≤ B * Real.exp (-c * Real.sqrt (Real.log X)) := by
      calc
        K = K * 1 := (mul_one _).symm
        _ ≤ K * (Real.exp (c * Real.sqrt (Real.log L)) *
            Real.exp (-c * Real.sqrt (Real.log X))) := mul_le_mul_of_nonneg_left he hK
        _ = (K * Real.exp (c * Real.sqrt (Real.log L))) *
            Real.exp (-c * Real.sqrt (Real.log X)) := (mul_assoc _ _ _).symm
        _ ≤ B * Real.exp (-c * Real.sqrt (Real.log X)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          dsimp [B]
          linarith
    exact hsmall'.trans (by
      have hh := mul_le_mul_of_nonneg_right hrate hXp
      simpa only [K, mul_right_comm] using hh)

end Ostmann

end OAI
