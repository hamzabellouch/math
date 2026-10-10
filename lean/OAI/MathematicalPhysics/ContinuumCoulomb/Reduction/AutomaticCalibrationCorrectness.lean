import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.AutomaticCalibrationProgram

namespace OAI

/-! The fixed polynomial-time distance program has the true Coulomb
calibration residual and geometric length bounds. All interval signs and
evaluation precision are discharged by the constructed program. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration

theorem exists_automatic_calibration (rho : ℕ) (hrho : 0 < rho)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (A B : ℕ) (kmin : ℝ) :
    ∃ (c : ℚ) (k : ℕ), 0 < c ∧ 0 < k ∧ kmin ≤ (k : ℝ) ∧
      ∀ (N P : ℕ) (K : ℚ), 2 ≤ N → ((N : ℝ) ^ A)⁻¹ ≤ K → (K : ℝ) ≤ (N : ℝ) ^ A →
        let d := value rho ε c k A B (N, (P, K))
        let D := (k : ℝ) * Real.log (N : ℝ)
        (1 - (ε : ℝ)) * D ≤ d ∧ (d : ℝ) ≤ (1 + (ε : ℝ)) * D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
              localizedCoulombProfile (GaussianFrequency.frequency rho) d ∧
          |(N : ℝ) ^ k * planarHopping d -
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N : ℝ) ^ B)⁻¹ K d| ≤
              ((P : ℝ) + 1)⁻¹ := by
  have hfreq : 0 < GaussianFrequency.frequency rho := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  obtain ⟨c, k, hc, hk, hkmin, hbracket⟩ :=
    CalibrationRationalBracket.exists_coulomb_brackets hfreq ε hε hε1 A B kmin
  refine ⟨c, k, hc, hk, hkmin, ?_⟩
  intro N P K hN hKlo hKhi
  let x : Input := (N, (P, K))
  let e := environment k A B x
  let p := interval ε c k N
  obtain ⟨ha, hb, _, hgap, hsign⟩ := hbracket N hN
  have hmem := value_mem (rho := rho) (k := k) (A := A) (B := B)
    x hε.le hc.le
  have hleft : (p.1 : ℝ) ≤ value rho ε c k A B x := by exact_mod_cast hmem.1
  have hright : (value rho ε c k A B x : ℝ) ≤ p.2 := by exact_mod_cast hmem.2
  have hK0 : (0 : ℝ) ≤ K := (inv_nonneg.mpr (by positivity)).trans hKlo
  have hKQ : (0 : ℚ) ≤ K := by exact_mod_cast hK0
  have hKbound : (K : ℝ) ≤ queryBound k A N := queryBound_coefficients k A N hKhi
  have hτ : (0 : ℚ) ≤ ((N ^ B : ℕ) : ℚ)⁻¹ := by positivity
  have hNB : (1 : ℚ) ≤ ((N ^ B : ℕ) : ℚ) := by
    exact_mod_cast (one_le_pow₀ (show 1 ≤ N by omega) : 1 ≤ N ^ B)
  have hτ1 : (((N ^ B : ℕ) : ℚ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hNB
  have hab : p.1 ≤ p.2 := interval_order hε.le hc.le k N
  have hquery := interval_query_bound hε1.le k A N ha hb hN
  have hs := hsign K hKlo hKhi
  have hsignA : 0 ≤ CalibratedEvaluation.residual rho e p.1 := by
    simpa only [CalibratedEvaluation.residual, e, environment, x, p, interval,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using hs.1
  have hsignB : CalibratedEvaluation.residual rho e p.2 ≤ 0 := by
    simpa only [CalibratedEvaluation.residual, e, environment, x, p, interval,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using hs.2
  have herr := CalibratedEvaluation.scheduled_residual rho hrho e p.1 p.2
    hKQ hKbound hτ hτ1 hab hquery.1 hquery.2 hsignA hsignB
    (fun r hr => hgap r hr.1)
  refine ⟨ha.trans hleft, hright.trans hb, hgap _ hleft, ?_⟩
  simpa only [value, CalibratedEvaluation.residual, e, environment, x, p, interval,
    Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using herr

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
