import OAI.NumberTheory.EgyptianFractions.VaughanRealTypeIHyperbolic

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.VaughanHyperbolic

/-- A common logarithmic majorant for both actual Type I costs. -/
theorem hyperbolicCost_min_le (N A q : ℕ) (hN : 1 ≤ N) (hq : 0 < q)
    (hqN : q ≤ N) :
    RealTypeI.hyperbolicCost N (min A N) q ≤
      8 * ((N : ℝ) / q + A + q) * (1 + Real.log (2 * (N : ℝ))) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hminA : ((min A N : ℕ) : ℝ) ≤ A := by exact_mod_cast min_le_left A N
  have hminN : ((min A N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right A N
  have hlogq : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (q : ℝ) by linarith)
    linarith
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (N : ℝ) by linarith)
    linarith
  have hlogqN : 1 + Real.log (2 * (q : ℝ)) ≤
      1 + Real.log (2 * (N : ℝ)) := by
    gcongr
  have hlogmin : 1 + Real.log (((min A N : ℕ) : ℝ) + 1) ≤
      1 + Real.log (2 * (N : ℝ)) := by
    exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith))
  unfold RealTypeI.hyperbolicCost
  calc
    _ ≤ 8 * ((A : ℝ) + q) * (1 + Real.log (2 * (N : ℝ))) +
        (4 * (N : ℝ) / q) * (1 + Real.log (2 * (N : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul (by gcongr) hlogqN hlogq (by positivity)
      · exact mul_le_mul_of_nonneg_left hlogmin (by positivity)
    _ ≤ _ := by
      have hd : 0 ≤ (N : ℝ) / q := by positivity
      simp only [mul_div_assoc]
      nlinarith [mul_nonneg hd hH]

private lemma log_le_common (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ≤ 1 + Real.log (2 * (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.log_le_log (show 0 < (N : ℝ) by linarith)
    (show (N : ℝ) ≤ 2 * N by linarith)
  linarith

/-- Uniform Type I bound in the parameters of the optimized Vaughan cutoff. -/
theorem first_typeI_normalized_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U : ℕ) (hN : 1 ≤ N) (hqN : q ≤ N) :
    ‖Vaughan.weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (Vaughan.shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      16 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * ((N : ℝ) / q + U + q) := by
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) :=
    (Real.log_natCast_nonneg N).trans (log_le_common N hN)
  calc
    _ ≤ 2 * Real.log N * RealTypeI.hyperbolicCost N (min U N) q :=
      first_typeI_real_phase_bound α a q hq hcop happrox N U
    _ ≤ 2 * Real.log N *
        (8 * ((N : ℝ) / q + U + q) * (1 + Real.log (2 * (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hyperbolicCost_min_le N U q hN hq hqN) (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (log_le_common N hN)
        (show 0 ≤ 16 * ((N : ℝ) / q + U + q) *
          (1 + Real.log (2 * (N : ℝ))) by positivity)
      nlinarith

/-- Uniform second Type I bound with the full product support retained. -/
theorem second_typeI_normalized_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V : ℕ) (hN : 1 ≤ N) (hqN : q ≤ N) :
    ‖Vaughan.weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (Vaughan.typeICoefficient U V * ζ)‖ ≤
      8 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * ((N : ℝ) / q + U * V + q) := by
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) :=
    (Real.log_natCast_nonneg N).trans (log_le_common N hN)
  calc
    _ ≤ Real.log N * RealTypeI.hyperbolicCost N (min (U * V) N) q :=
      second_typeI_real_phase_bound α a q hq hcop happrox N U V
    _ ≤ Real.log N *
        (8 * ((N : ℝ) / q + (U * V : ℕ) + q) * (1 + Real.log (2 * (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hyperbolicCost_min_le N (U * V) q hN hq hqN)
        (Real.log_natCast_nonneg N)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (log_le_common N hN)
        (show 0 ≤ 8 * ((N : ℝ) / q + U * V + q) *
          (1 + Real.log (2 * (N : ℝ))) by positivity)
      push_cast
      nlinarith

end Problem337.VaughanHyperbolic

end

end OAI
