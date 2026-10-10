import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepListProgram

namespace OAI

/-! The particular sparse, nonempty circuit used by the history reduction,
with its literal program and unchanged verifier acceptance probability. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram
open BinaryEncoding

def qmaPreparedCircuit (c : QMACircuit) : QMACircuit :=
  qmaSparseCircuit (qmaNonemptyCircuit c)

theorem qmaPreparedCircuit_witness (c : QMACircuit) :
    (qmaPreparedCircuit c).witness=c.witness := rfl

theorem qmaPreparedCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaPreparedCircuit c).WellFormed :=
  qmaSparseCircuit_wellFormed _ (qmaNonemptyCircuit_wellFormed c hc)

theorem qmaPreparedCircuit_positive (c : QMACircuit) :
    0 < (qmaPreparedCircuit c).gates.length := qmaNonemptyCircuit_sparse_pos c

theorem qmaPreparedCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaPreparedCircuit c) (qmaPreparedCircuit_wellFormed c hc) psi=
      qmaAcceptance c hc psi := by
  exact (qmaSparseCircuit_acceptance (qmaNonemptyCircuit c)
    (qmaNonemptyCircuit_wellFormed c hc) psi).trans
      (qmaNonemptyCircuit_acceptance c hc psi)

theorem qmaPreparedCircuit_size (c : QMACircuit) {B : ℕ}
    (hB : c.work+c.gates.length ≤ B) :
    (qmaPreparedCircuit c).work+(qmaPreparedCircuit c).gates.length ≤
      B+(4*B+5)*(6*B+7)*(B+2) := by
  have hw : c.work ≤ B := by omega
  have hg : c.gates.length ≤ B := by omega
  have h := qmaSparseCircuit_size (qmaNonemptyCircuit c)
  change (qmaPreparedCircuit c).work+(qmaPreparedCircuit c).gates.length ≤ _ at h
  have hs : (qmaPreparedCircuit c).work+(qmaPreparedCircuit c).gates.length ≤
      c.work+(4*c.work+5)*(6*c.work+7)*(c.gates.length+2) := by
    simpa only [qmaNonemptyCircuit,List.length_append,List.length_cons,List.length_nil,
      Nat.add_zero] using h
  exact hs.trans (by gcongr)

namespace QuantumCircuitCode

noncomputable def preparedCircuitProgram : Procedure circuitCode circuitCode qmaPreparedCircuit :=
  sparseCircuitProgram.comp nonemptyProgram

end QuantumCircuitCode

def QuantumVerifier.prepared (V : QuantumVerifier) (x : BitString) : QMACircuit :=
  qmaPreparedCircuit (V.generate x)

theorem QuantumVerifier.prepared_wellFormed (V : QuantumVerifier) (x : BitString) :
    (V.prepared x).WellFormed := qmaPreparedCircuit_wellFormed _ (V.wellFormed x)

theorem QuantumVerifier.prepared_positive (V : QuantumVerifier) (x : BitString) :
    0 < (V.prepared x).gates.length := qmaPreparedCircuit_positive _

def QuantumVerifier.preparedSize (V : QuantumVerifier) : Polynomial ℕ :=
  V.size+(4*V.size+5)*(6*V.size+7)*(V.size+2)

theorem QuantumVerifier.prepared_size (V : QuantumVerifier) (x : BitString) :
    (V.prepared x).work+(V.prepared x).gates.length ≤ V.preparedSize.eval x.length := by
  simpa only [prepared,preparedSize,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_natCast,Polynomial.eval_ofNat] using
      qmaPreparedCircuit_size (V.generate x) (V.size_bound x)

end ContinuumCoulomb

end

end OAI
