import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZScalarSample

namespace OAI

/-! The sampled rational exchange Hamiltonian approximates the entire logical X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def matrixValue (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  qmaExchangeMatrix
    (qmaFourExchangeLeft (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
      (fun e => (qmaXZFieldData t e).site))
    (qmaFourExchangeRight (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
      (fun e => (qmaXZFieldData t e).site))
    (fun x => (weightValue k r
      (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
      (fun e => J e.val) (fun e => (qmaXZFieldData t e).axis) (fun e => J e.val) x:ℝ))
    (scalarValue k r t J:ℝ)

def matrixErrorBudget (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) : ℝ :=
  3*(Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)):ℝ)*
    weightErrorBudget (r:ℝ) (qmaXZInputSize (fun e => (J e:ℝ)))+320800*(∑ e, |(J e:ℝ)|)

theorem matrixValue_error (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    |MediatorGraph.normalizedBottom (matrixValue k r t J)-
      MediatorGraph.normalizedBottom (qmaXZBlockSource (r:ℝ) t (fun e => (J e:ℝ)))| ≤
        matrixErrorBudget r t J*(2:ℝ)⁻¹^k := by
  have hB : 0 ≤ qmaXZInputSize (fun e => (J e:ℝ)) := by unfold qmaXZInputSize; positivity
  have hJ (e : κ) : |(J e:ℝ)| ≤ qmaXZInputSize (fun e => (J e:ℝ)) := by
    apply (Finset.single_le_sum (fun f _ => abs_nonneg (J f:ℝ)) (Finset.mem_univ e)).trans
    unfold qmaXZInputSize
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact weightValue_ground_error k r
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).distinct)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val) (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (scalarValue k r t J) (qmaXZFamilyConstant t (fun e => (J e:ℝ)))
    (qmaXZInputSize (fun e => (J e:ℝ))) (320800*(∑ e, |(J e:ℝ)|)) hB
    (fun e => hJ e.val) (fun e => hJ e.val) (scalarValue_error k r t J)

def rationalInputSize (J : κ → ℚ) : ℚ := Fintype.card κ+∑ e, |J e|
def rationalBudget (J : κ → ℚ) : ℚ := 1+2000000*rationalInputSize J+(7056*rationalInputSize J)^2
def rationalPenalty (N : ℕ) (J : κ → ℚ) : ℚ := 9*(rationalBudget J)^3*N

theorem rationalBudget_cast (J : κ → ℚ) :
    (rationalBudget J:ℝ) = qmaXZPolynomialBudget (fun e => (J e:ℝ)) := by
  simp only [rationalBudget,rationalInputSize,qmaXZPolynomialBudget,qmaXZInputSize,
    Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_sum,Rat.cast_abs,Rat.cast_one]

theorem matrixValue_accuracy (k N : ℕ) (hN : 0 < N) (t : κ → QMAXZTerm n) (J : κ → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (matrixValue k (rationalPenalty N J) t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤
        matrixErrorBudget (rationalPenalty N J) t J*(2:ℝ)⁻¹^k+1/(N:ℝ) := by
  have hsample := matrixValue_error k (rationalPenalty N J) t J
  have hphys := qmaXZBlock_polynomial_accuracy t (fun e => (J e:ℝ)) hprivate N hN
  have hcast : (rationalPenalty N J:ℝ) = 9*(qmaXZPolynomialBudget (fun e => (J e:ℝ)))^3*N := by
    simp only [rationalPenalty,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,rationalBudget_cast]
  rw [← hcast] at hphys
  simpa only [Complex.ofReal_ratCast] using (abs_sub_le _ _ _).trans (add_le_add hsample hphys)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
