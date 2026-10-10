import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumComputedAccuracy

namespace OAI

/-! A computable budget uses only the qubit count, term count and coefficient mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

def universalErrorBudget (n m : ℕ) (r S : ℚ) : ℚ :=
  3*(6*n+25*m)*(1568*|r| *(1+(m+S))+26064*(m+S))+320800*S

variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem rationalErrorBudget_le (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    rationalErrorBudget r t J ≤ universalErrorBudget n (Fintype.card κ) r (∑ e, |J e|) := by
  have hc : (Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)):ℚ) ≤
      6*n+25*Fintype.card κ := by exact_mod_cast qmaXZBlock_exchange_count t
  have hU : (0:ℚ) ≤ Fintype.card κ+∑ e, |J e| := by positivity
  unfold rationalErrorBudget universalErrorBudget rationalInputSize
  gcongr

def boundedPrecision (N : ℕ) (_t : κ → QMAXZTerm n) (J : κ → ℚ) : ℕ :=
  precision (universalErrorBudget n (Fintype.card κ) (rationalPenalty N J) (∑ e, |J e|)) N

def boundedMatrix (N : ℕ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  matrixValue (boundedPrecision N t J) (rationalPenalty N J) t J

theorem boundedMatrix_accuracy (N : ℕ) (hN : 0 < N) (t : κ → QMAXZTerm n) (J : κ → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (boundedMatrix N t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  have h := matrixValue_accuracy (boundedPrecision N t J) N hN t J hprivate
  have he := precision_error
    (universalErrorBudget n (Fintype.card κ) (rationalPenalty N J) (∑ e, |J e|)) N hN
  have hb : matrixErrorBudget (rationalPenalty N J) t J ≤
      (universalErrorBudget n (Fintype.card κ) (rationalPenalty N J) (∑ e, |J e|):ℝ) := by
    rw [← rationalErrorBudget_cast]
    exact_mod_cast rationalErrorBudget_le (rationalPenalty N J) t J
  have he' := (mul_le_mul_of_nonneg_right hb
    (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹^(boundedPrecision N t J))).trans he
  apply h.trans
  calc
    _ ≤ 1/(N:ℝ)+1/(N:ℝ) := add_le_add he' le_rfl
    _ = 2/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
