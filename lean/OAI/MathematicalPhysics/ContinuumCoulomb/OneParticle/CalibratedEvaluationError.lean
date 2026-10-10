import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationBudget

namespace OAI

/-! Certified evaluation of the actual calibrated hopping residual,
uniformly on rational points in a bounded interval. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

theorem approximation_error (rho : ℕ) (hrho : 0 < rho) (e : Environment) (d : ℚ)
    (hK : (0 : ℚ) ≤ e.2.2.2) (hKN : (e.2.2.2 : ℝ) ≤ e.1.1)
    (hτ : (0 : ℚ) ≤ e.2.2.1) (hτ1 : e.2.2.1 ≤ 1)
    (hd : |(d : ℝ)| ≤ (e.1.1 : ℝ))
    (hgap : 0 ≤ localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
      localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ)) :
    |(value rho e d : ℝ) -
      ((e.2.1 : ℝ) * planarHopping (d : ℝ) - (e.2.2.1 : ℝ) *
        Real.sqrt ((e.2.2.2 : ℝ) *
          (localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
            localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ))))| ≤
      ((e.1.2 : ℝ) + 1)⁻¹ := by
  have hKr : (0 : ℝ) ≤ e.2.2.2 := by exact_mod_cast hK
  have hτr : (0 : ℝ) ≤ e.2.2.1 := by exact_mod_cast hτ
  have hτ1r : (e.2.2.1 : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hu := CoulombEvaluation.approximation_error rho (coulombPrecision e.1.1 e.1.2) hrho 0
  have hv := CoulombEvaluation.approximation_error rho (coulombPrecision e.1.1 e.1.2) hrho d
  simp only [Rat.cast_zero] at hu
  have ht := ComputableHopping.approximation_error
    ((e.1.1, hoppingPrecision e.2.1 e.1.2), d) hd
  have hq : (0 : ℚ) ≤ e.2.2.2 * gap rho e.1.1 e.1.2 d :=
    mul_nonneg hK (le_max_left _ _)
  have hr := RationalSquareRoot.value_error (rootPrecision e.1.2) hq
  have hr' : |(root rho e.1.1 e.1.2 e.2.2.2 d : ℝ) -
      Real.sqrt ((e.2.2.2 : ℝ) * max 0
        ((CoulombEvaluation.approximate rho (coulombPrecision e.1.1 e.1.2) 0 : ℝ) -
          CoulombEvaluation.approximate rho (coulombPrecision e.1.1 e.1.2) d))| ≤
      (2 : ℝ)⁻¹ ^ rootPrecision e.1.2 := by
    simpa only [root, gap, Rat.cast_mul, Rat.cast_max, Rat.cast_zero, Rat.cast_sub] using hr
  have he := calibrated_residual_error (Nat.cast_nonneg e.2.1) hτr hKr hgap ht hu hv hr'
  have hhop := hopping_budget e.2.1 e.1.2
  have hroot := root_budget e.1.2
  have hcoulomb := coulomb_root_budget e.1.1 e.1.2 hKN
  have hnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ rootPrecision e.1.2 +
      Real.sqrt (2 * (e.2.2.2 : ℝ) * ((coulombPrecision e.1.1 e.1.2 : ℝ) + 1)⁻¹) := by
    positivity
  have htarget := mul_le_mul_of_nonneg_right hτ1r hnonneg
  have hfinal := he.trans (add_le_add hhop
    (htarget.trans (by simpa only [one_mul] using add_le_add hroot hcoulomb)))
  have hsum : (4 * ((e.1.2 : ℝ) + 1))⁻¹ +
      ((4 * ((e.1.2 : ℝ) + 1))⁻¹ + (4 * ((e.1.2 : ℝ) + 1))⁻¹) =
      3 * (4 * ((e.1.2 : ℝ) + 1))⁻¹ := by ring
  have hout : |(value rho e d : ℝ) -
      ((e.2.1 : ℝ) * planarHopping (d : ℝ) - (e.2.2.1 : ℝ) *
        Real.sqrt ((e.2.2.2 : ℝ) *
          (localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
            localizedCoulombProfile (GaussianFrequency.frequency rho) (d : ℝ))))| ≤
      3 * (4 * ((e.1.2 : ℝ) + 1))⁻¹ := by
    simpa only [value, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, hsum] using hfinal
  apply hout.trans
  rw [mul_inv]
  norm_num
  nlinarith [inv_pos.mpr (show (0 : ℝ) < e.1.2 + 1 by positivity)]

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
