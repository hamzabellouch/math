import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalLogScale

namespace OAI

/-! Rational endpoints lie inside the permitted contact interval and outside
the smaller interval used for the analytic sign estimates. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

def endpoints (ε q : ℚ) : ℚ × ℚ := ((1 - ε / 2) * q, (1 + ε / 2) * q)

theorem endpoint_bounds {ε D q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hD : 0 ≤ D)
    (hqlo : (1 - ε / 16) * D ≤ q) (hqhi : q ≤ (1 + ε / 16) * D) :
    (1 - ε) * D ≤ (1 - ε / 2) * q ∧
      (1 - ε / 2) * q ≤ (1 - ε / 4) * D ∧
      (1 + ε / 4) * D ≤ (1 + ε / 2) * q ∧
      (1 + ε / 2) * q ≤ (1 + ε) * D := by
  have hc0 : 0 ≤ 1 - ε / 2 := by linarith
  have hc1 : 0 ≤ 1 + ε / 2 := by linarith
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have ha0 : 1 - ε ≤ (1 - ε / 2) * (1 - ε / 16) := by nlinarith [sq_nonneg ε]
  have ha1 : (1 - ε / 2) * (1 + ε / 16) ≤ 1 - ε / 4 := by nlinarith [sq_nonneg ε]
  have hb0 : 1 + ε / 4 ≤ (1 + ε / 2) * (1 - ε / 16) := by nlinarith
  have hb1 : (1 + ε / 2) * (1 + ε / 16) ≤ 1 + ε := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right ha0 hD).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hqlo hc0)
  · exact (mul_le_mul_of_nonneg_left hqhi hc0).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ha1 hD)
  · exact (mul_le_mul_of_nonneg_right hb0 hD).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hqlo hc1)
  · exact (mul_le_mul_of_nonneg_left hqhi hc1).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb1 hD)

theorem rational_endpoint_bounds (ε c : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : |(c : ℝ) - Real.log 2| ≤ (ε : ℝ) / 64 * Real.log 2)
    (k N : ℕ) (hN : 2 ≤ N) (hk : 128 ≤ (ε : ℝ) * (k : ℝ)) :
    let D := (k : ℝ) * Real.log (N : ℝ)
    let p := endpoints ε (RationalLogScale.value c k N)
    (1 - (ε : ℝ)) * D ≤ p.1 ∧ p.1 ≤ (1 - (ε : ℝ) / 4) * D ∧
      (1 + (ε : ℝ) / 4) * D ≤ p.2 ∧ p.2 ≤ (1 + (ε : ℝ)) * D := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hc' : |(c : ℝ) - Real.log 2| ≤ ((ε : ℝ) / 16) / 4 * Real.log 2 := by
    convert hc using 1; ring
  have hk' : 8 ≤ ((ε : ℝ) / 16) * (k : ℝ) := by nlinarith
  obtain ⟨hlo, hhi⟩ := RationalLogScale.relative_bounds c
    (show 0 < (ε : ℝ) / 16 by positivity) (show (ε : ℝ) / 16 ≤ 1 by linarith)
    hc' k N hN hk'
  have hD : 0 ≤ (k : ℝ) * Real.log (N : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  simpa only [endpoints, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using endpoint_bounds hεR hεR1 hD hlo hhi

end ContinuumCoulomb.CalibrationRationalBracket

end

end OAI
