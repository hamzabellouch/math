import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryPrefixCertificate
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPolynomialUnary
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPreparedCircuit

namespace OAI

/-! The actual verifier generator followed by the sparse-circuit compiler.
The unary size certificate is computed from the original input and retained
through the arbitrary given generator before its binary registers are parsed. -/

noncomputable section
namespace ContinuumCoulomb
open Turing ExactQuantumFactoring.BitStackProgram BinaryEncoding

namespace QuantumVerifier

noncomputable def prefixProgram (V : QuantumVerifier) :
    Procedure (id : BitString → List Bool) (prodCode unaryCode id)
      (fun x => (V.size.eval x.length,x)) :=
  ((QuantumPolynomialUnary.program V.size).comp Procedure.length).pair
    (Procedure.identity id)

noncomputable def generateUnary (V : QuantumVerifier) :
    TM2ComputableInPolyTime (id : BitString → List Bool)
      QuantumCircuitCode.circuitCode V.generate := by
  let prefixed := TM2Composition.computable (prefixProgram V).toTM2
    (QuantumUnaryPrefix.computable V.uniform)
  let parsed := TM2Composition.computable prefixed QuantumCircuitCode.boundedInput.toTM2
  have he : QuantumCircuitCode.cap ∘
      ((fun x : ℕ × BitString => (x.1,V.generate x.2)) ∘
        (fun x : BitString => (V.size.eval x.length,x))) = V.generate := by
    funext x
    exact QuantumCircuitCode.cap_eq_of_wellFormed _ _ (V.wellFormed x)
      (by
        change (V.generate x).work ≤ V.size.eval x.length
        have hh := V.size_bound x
        omega)
  change TM2ComputableInPolyTime id QuantumCircuitCode.circuitCode
    (QuantumCircuitCode.cap ∘
      ((fun x : ℕ × BitString => (x.1,V.generate x.2)) ∘
        (fun x : BitString => (V.size.eval x.length,x)))) at parsed
  rw [he] at parsed
  exact parsed

noncomputable def preparedUniform (V : QuantumVerifier) :
    TM2ComputableInPolyTime (id : BitString → List Bool)
      QuantumCircuitCode.circuitCode V.prepared :=
  TM2Composition.computable V.generateUnary QuantumCircuitCode.preparedCircuitProgram.toTM2

theorem prepared_complete (V : QuantumVerifier) (x : BitString)
    (hc : ∃ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖=1 ∧ 2/3 ≤ qmaAcceptance (V.generate x) (V.wellFormed x) psi) :
    ∃ psi : EuclideanSpace ℂ (SourceSpinBasis (V.prepared x).witness),
      ‖psi‖=1 ∧ 2/3 ≤ qmaAcceptance (V.prepared x) (V.prepared_wellFormed x) psi := by
  rcases hc with ⟨psi,hpsi,haccept⟩
  refine ⟨psi,hpsi,?_⟩
  exact (qmaPreparedCircuit_acceptance (V.generate x) (V.wellFormed x) psi).symm ▸ haccept

theorem prepared_sound (V : QuantumVerifier) (x : BitString)
    (hc : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖=1 → qmaAcceptance (V.generate x) (V.wellFormed x) psi ≤ 1/3) :
    ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (V.prepared x).witness),
      ‖psi‖=1 → qmaAcceptance (V.prepared x) (V.prepared_wellFormed x) psi ≤ 1/3 := by
  intro psi hpsi
  exact (qmaPreparedCircuit_acceptance (V.generate x) (V.wellFormed x) psi).symm ▸ hc psi hpsi

end QuantumVerifier
end ContinuumCoulomb

end

end OAI
