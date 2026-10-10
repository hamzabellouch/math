import OAI.NumberTheory.EgyptianFractions.ChebyshevLowerSharp
import OAI.NumberTheory.EgyptianFractions.ChebyshevImprovedLower
import OAI.NumberTheory.EgyptianFractions.DilationRecurrenceUpper

namespace OAI
noncomputable section
open Filter

namespace Problem337.ChebyshevUpperSharp

/-- The classical upper Chebyshev constant, approximately `1.10555`. -/
def upperConstant : ℝ := 6 * ChebyshevLowerSharp.lowerConstant / 5

lemma upperConstant_pos : 0 < upperConstant := by
  have h := ChebyshevLowerSharp.lowerConstant_gt_921_div_1000
  dsimp [upperConstant]
  linarith

lemma upperConstant_lt_1106_div_1000 : upperConstant < (1106 / 1000 : ℝ) := by
  rw [upperConstant, ChebyshevLowerSharp.lowerConstant_eq]
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

/-- The exact finite dilation recurrence and the factorial ratio limit give
the classical sharp elementary upper coefficient for `psi`. -/
theorem eventually_psi_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Chebyshev.psi N ≤ (upperConstant + ε) * (N : ℝ) := by
  have hc : 0 ≤ ChebyshevLowerSharp.lowerConstant := by
    linarith [ChebyshevLowerSharp.lowerConstant_gt_921_div_1000]
  have hrec : ∀ᶠ N : ℕ in atTop, Chebyshev.psi N ≤
      ChebyshevLowerSharp.factorialCombination N + Chebyshev.psi (N / 6 : ℕ) :=
    Eventually.of_forall chebyshev_psi_le_factorial_combination_add
  have h := DilationRecurrence.eventually_upper_of_ratio_limit
    (fun N => Chebyshev.psi N) ChebyshevLowerSharp.factorialCombination
    6 (by norm_num) ChebyshevLowerSharp.lowerConstant hc hrec
    ChebyshevLowerSharp.factorialCombination_div_tendsto ε hε
  have heq : ChebyshevLowerSharp.lowerConstant / (1 - 1 / (6 : ℝ)) =
      upperConstant := by dsimp [upperConstant]; ring
  simpa only [Nat.cast_ofNat, heq] using h

theorem eventually_theta_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Chebyshev.theta N ≤ (upperConstant + ε) * (N : ℝ) := by
  filter_upwards [eventually_psi_upper ε hε] with N hN
  exact (Chebyshev.theta_le_psi N).trans hN

/-- The classical partial-summation remainder is already lower order. Hence
an improved eventual coefficient for `theta` transfers without a fixed loss
to the actual prime counting function. -/
theorem eventually_primeCounting_upper_of_theta (c ε : ℝ) (hε : 0 < ε)
    (hθ : ∀ᶠ N : ℕ in atTop, Chebyshev.theta N ≤ c * (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤ (c + ε) * (N : ℝ) / Real.log (N : ℝ) := by
  have herr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.integral_theta_div_log_sq_isLittleO.bound hε)
  filter_upwards [hθ, herr, eventually_ge_atTop (2 : ℕ)] with N hN he hN2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (show (2 : ℝ) ≤ N by exact_mod_cast hN2)
  simp only [Nat.floor_natCast] at hid
  rw [Real.norm_of_nonneg (div_nonneg hN0 hlog.le)] at he
  have hi := (Real.le_norm_self
    (∫ t in (2 : ℝ)..(N : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2))).trans he
  calc
    (Nat.primeCounting N : ℝ) = Chebyshev.theta N / Real.log (N : ℝ) +
        ∫ t in (2 : ℝ)..(N : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2) := hid
    _ ≤ (c * (N : ℝ)) / Real.log (N : ℝ) +
        ε * ((N : ℝ) / Real.log (N : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right hN hlog.le) hi
    _ = _ := by ring

/-- The classical upper Chebyshev coefficient transfers to actual primes. -/
theorem eventually_primeCounting_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤
        (upperConstant + ε) * (N : ℝ) / Real.log (N : ℝ) := by
  have hhalf : 0 < ε / 2 := by positivity
  have h := eventually_primeCounting_upper_of_theta (upperConstant + ε / 2)
    (ε / 2) hhalf (eventually_theta_upper (ε / 2) hhalf)
  have heq : upperConstant + ε / 2 + ε / 2 = upperConstant + ε := by ring
  simpa only [heq] using h

theorem eventually_primeCounting_upper_1106 :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤
        (1106 / 1000 : ℝ) * (N : ℝ) / Real.log (N : ℝ) := by
  have h := eventually_primeCounting_upper ((1106 / 1000 : ℝ) - upperConstant)
    (sub_pos.mpr upperConstant_lt_1106_div_1000)
  simpa only [add_sub_cancel] using h

end Problem337.ChebyshevUpperSharp

end

end OAI
