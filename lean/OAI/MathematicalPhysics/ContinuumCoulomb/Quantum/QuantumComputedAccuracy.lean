import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSamplePrecision

namespace OAI

/-! A computable binary-precision choice closes the full rational four-spin error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def rationalErrorBudget (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℚ :=
  3*Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t))*
    (1568*|r| *(1+rationalInputSize J)+26064*rationalInputSize J)+320800*(∑ e, |J e|)

theorem rationalErrorBudget_cast (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    (rationalErrorBudget r t J:ℝ) = matrixErrorBudget r t J := by
  simp only [rationalErrorBudget,matrixErrorBudget,weightErrorBudget,rationalInputSize,qmaXZInputSize,
    Rat.cast_add,Rat.cast_mul,Rat.cast_abs,Rat.cast_sum,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast]

def outputPrecision (N : ℕ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℕ :=
  precision (rationalErrorBudget (rationalPenalty N J) t J) N

def outputMatrix (N : ℕ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  matrixValue (outputPrecision N t J) (rationalPenalty N J) t J

theorem outputMatrix_accuracy (N : ℕ) (hN : 0 < N) (t : κ → QMAXZTerm n) (J : κ → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (outputMatrix N t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  have h := matrixValue_accuracy (outputPrecision N t J) N hN t J hprivate
  have he := precision_error (rationalErrorBudget (rationalPenalty N J) t J) N hN
  rw [rationalErrorBudget_cast] at he
  change matrixErrorBudget (rationalPenalty N J) t J*(2:ℝ)⁻¹^(outputPrecision N t J) ≤ 1/(N:ℝ) at he
  apply h.trans
  calc
    _ ≤ 1/(N:ℝ)+1/(N:ℝ) := add_le_add he le_rfl
    _ = 2/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
