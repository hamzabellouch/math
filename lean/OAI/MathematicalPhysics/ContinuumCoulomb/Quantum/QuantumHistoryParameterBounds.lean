import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryOutputBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientEnvelopeProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPromisePowers
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFinalPrecision

namespace OAI

/-! Uniform polynomial powers for the actual history coefficients. These
bounds are in the retained history-qubit count, not in an auxiliary circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory
open QuantumCoefficientPrograms

def parameterEnvelope (rounds n : ℕ) : ℕ :=
  n+8192*n+128*(14+288*((14*(n+1)+8)*n))+60*(rounds+9)*(n+1)+1

theorem parameterEnvelope_power (rounds : ℕ) : ∃ k : ℕ, ∀ n,
    parameterEnvelope rounds n ≤ (n+2)^k := by
  let p : Polynomial ℕ := Polynomial.X+8192*Polynomial.X+
    128*(14+288*((14*(Polynomial.X+1)+8)*Polynomial.X))+
    Polynomial.C (60*(rounds+9))*(Polynomial.X+1)+1
  obtain ⟨k,hk⟩ := natPolynomial_power_bound p
  refine ⟨k,fun n => ?_⟩
  simpa only [p,parameterEnvelope,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_natCast,Polynomial.eval_ofNat,
    Polynomial.eval_one] using hk n

theorem qubitCount_positive (c : QMACircuit) : 0 < qubitCount c := by
  rw [qubitCount_eq]
  omega

theorem time_le_qubitCount (c : QMACircuit) : c.gates.length ≤ qubitCount c := by
  rw [qubitCount_eq]
  omega

theorem termCount_bound (c : QMACircuit) : termCount c ≤ 8192*qubitCount c := by
  rw [termCount_eq,qubitCount_eq]
  omega

theorem parameters_le_envelope (rounds : ℕ) (c : QMACircuit) :
    qubitCount c ≤ parameterEnvelope rounds (qubitCount c) ∧
    termCount c ≤ parameterEnvelope rounds (qubitCount c) ∧
    coefficientBudget c ≤ parameterEnvelope rounds (qubitCount c) ∧
    finalPrecision rounds c ≤ parameterEnvelope rounds (qubitCount c) := by
  have hwork : c.work+1 ≤ qubitCount c+1 := by rw [qubitCount_eq]; omega
  have htime : c.gates.length ≤ qubitCount c := by rw [qubitCount_eq]; omega
  have ht := termCount_bound c
  have hb : coefficientBudget c ≤
      128*(14+288*((14*(qubitCount c+1)+8)*qubitCount c)) := by
    unfold coefficientBudget
    gcongr
  have hp : finalPrecision rounds c ≤ 60*(rounds+9)*(qubitCount c+1) := by
    unfold finalPrecision
    gcongr
  unfold parameterEnvelope
  omega

theorem parameters_power (rounds : ℕ) : ∃ k : ℕ, ∀ c : QMACircuit,
    qubitCount c ≤ (qubitCount c+2)^k ∧
    termCount c ≤ (qubitCount c+2)^k ∧
    coefficientBudget c ≤ (qubitCount c+2)^k ∧
    finalPrecision rounds c ≤ (qubitCount c+2)^k := by
  obtain ⟨k,hk⟩ := parameterEnvelope_power rounds
  refine ⟨k,fun c => ?_⟩
  obtain ⟨h₁,h₂,h₃,h₄⟩ := parameters_le_envelope rounds c
  exact ⟨h₁.trans (hk _),h₂.trans (hk _),h₃.trans (hk _),h₄.trans (hk _)⟩

theorem historyCoefficientBudget_power (rounds : ℕ) : ∃ k : ℕ, ∀ c : QMACircuit,
    historyCoefficientBudget c (finalPrecision rounds c) ≤ (qubitCount c+2)^k := by
  obtain ⟨a,ha⟩ := parameters_power rounds
  obtain ⟨b,hb⟩ := QuantumCoefficientEnvelopeProgram.polynomial_bound
  refine ⟨(a+4)*b,fun c => ?_⟩
  obtain ⟨hn,hm,hB,hN⟩ := ha c
  exact lattice_function_power hb hn hm hB hN

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
