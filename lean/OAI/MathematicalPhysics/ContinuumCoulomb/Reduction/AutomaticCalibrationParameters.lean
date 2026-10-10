import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationCoulombBrackets
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CalibrationRationalBracketProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CalibratedBisectionProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisectionLocation

namespace OAI

/-! Input and query bounds for the automatic calibrated-distance program.
The unary evaluator range is a fixed polynomial in the source size. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration

abbrev Input := ℕ × (ℕ × ℚ)

def queryBound (k A N : ℕ) : ℕ := 2 * k * N + N ^ A + 1

def environment (k A B : ℕ) (x : Input) : CalibratedEvaluation.Environment :=
  ((queryBound k A x.1, x.2.1), (x.1 ^ k, (((x.1 ^ B : ℕ) : ℚ)⁻¹, x.2.2)))

def interval (ε c : ℚ) (k N : ℕ) : ℚ × ℚ :=
  CalibrationRationalBracket.endpoints ε (RationalLogScale.value c k N)

def value (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : ℚ :=
  CalibratedEvaluation.scheduledValue rho (environment k A B x)
    (interval ε c k x.1).1 (interval ε c k x.1).2

theorem interval_order {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (k N : ℕ) :
    (interval ε c k N).1 ≤ (interval ε c k N).2 := by
  have hq : (0 : ℚ) ≤ RationalLogScale.value c k N :=
    mul_nonneg hc (Nat.cast_nonneg _)
  dsimp only [interval, CalibrationRationalBracket.endpoints]
  nlinarith [mul_nonneg hε hq]

theorem queryBound_coefficients (k A : ℕ) (N : ℕ) {K : ℚ}
    (hK : (K : ℝ) ≤ (N : ℝ) ^ A) : (K : ℝ) ≤ queryBound k A N := by
  have hcast : (N : ℝ) ^ A ≤ (queryBound k A N : ℝ) := by
    exact_mod_cast (show N ^ A ≤ queryBound k A N by unfold queryBound; omega)
  exact hK.trans hcast

theorem interval_query_bound {ε c : ℚ} (hε1 : ε ≤ 1) (k A N : ℕ)
    (ha : (1 - (ε : ℝ)) * ((k : ℝ) * Real.log N) ≤ (interval ε c k N).1)
    (hb : ((interval ε c k N).2 : ℝ) ≤ (1 + (ε : ℝ)) * ((k : ℝ) * Real.log N))
    (hN : 2 ≤ N) :
    -(queryBound k A N : ℝ) ≤ (interval ε c k N).1 ∧
      ((interval ε c k N).2 : ℝ) ≤ queryBound k A N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hD : 0 ≤ (k : ℝ) * Real.log N := mul_nonneg (Nat.cast_nonneg _) hlog
  have hlow : (0 : ℝ) ≤ (interval ε c k N).1 :=
    (mul_nonneg (sub_nonneg.mpr hεR1) hD).trans ha
  have hupper : ((interval ε c k N).2 : ℝ) ≤ 2 * k * N := by
    calc
      _ ≤ (1 + (ε : ℝ)) * ((k : ℝ) * Real.log N) := hb
      _ ≤ 2 * ((k : ℝ) * Real.log N) := by gcongr; linarith
      _ ≤ 2 * ((k : ℝ) * N) := by
        gcongr
        exact Real.log_le_self (by positivity)
      _ = _ := by ring
  have hbound : 2 * (k : ℝ) * N ≤ (queryBound k A N : ℝ) := by
    exact_mod_cast (show 2 * k * N ≤ queryBound k A N by unfold queryBound; omega)
  exact ⟨(neg_nonpos.mpr (Nat.cast_nonneg _)).trans hlow, hupper.trans hbound⟩

theorem value_mem {ε c : ℚ} (rho k A B : ℕ) (x : Input)
    (hε : 0 ≤ ε) (hc : 0 ≤ c) :
    value rho ε c k A B x ∈ Set.Icc (interval ε c k x.1).1 (interval ε c k x.1).2 :=
  CalibratedEvaluation.scheduledValue_mem rho (environment k A B x)
    (interval ε c k x.1).1 (interval ε c k x.1).2 (interval_order hε hc k x.1)

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
