import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryLiteralPromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryLiteralCorrectness

namespace OAI

/-!
QMA hardness of the field-free signed square-lattice Heisenberg
problem through a polynomial circuit compiler and full-space energy bounds.
-/

noncomputable section
namespace ContinuumCoulomb

theorem publishedCMPHardness : PublishedCMPHardness := by
  obtain ⟨k,hk,hpromise⟩ := QuantumHistorySourceProgram.circuit_polynomialPromise
  refine ⟨k,hk,?_⟩
  intro P hP
  obtain ⟨V,hyes,hno⟩ := hP
  refine ⟨{
    map := QuantumHistorySourceProgram.fromVerifier V
    polynomialTime := QuantumHistorySourceProgram.fromVerifier_uniform V
    maps_yes := ?_
    maps_no := ?_
  }⟩
  · intro x hx
    obtain ⟨psi,hpsi,ha⟩ := hyes x hx
    exact QuantumHistorySourceProgram.literal_accepting (V.generate x) (V.wellFormed x)
      (hpromise _ (V.wellFormed x)) psi hpsi ha
  · intro x hx
    exact QuantumHistorySourceProgram.literal_rejecting (V.generate x) (V.wellFormed x)
      (hpromise _ (V.wellFormed x)) (hno x hx)

end ContinuumCoulomb

end

end OAI
