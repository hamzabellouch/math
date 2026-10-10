import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumVerifier

namespace OAI

/-! The finite circuit acceptance promise, with its actual polynomial
reduction from every verifier in the fixed QMA model. -/

noncomputable section
open Set
namespace ContinuumCoulomb

def qmaCircuitPromise : PromiseProblem QMACircuit where
  yes := {c | ∃ hc : c.WellFormed,
    ∃ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 ∧ 2/3 ≤ qmaAcceptance c hc psi}
  no := {c | ∃ hc : c.WellFormed,
    ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro c ⟨hc,psi,hpsi,hyes⟩ ⟨hc',hno⟩
    have hn := hno psi hpsi
    linarith

theorem qmaCircuitPromise_qmaHard : QMAHard qmaCircuitCodec.encode qmaCircuitPromise := by
  rintro P ⟨V,hyes,hno⟩
  refine ⟨{ map := V.generate, polynomialTime := V.uniform, maps_yes := ?_, maps_no := ?_ }⟩
  · intro x hx
    exact ⟨V.wellFormed x,hyes x hx⟩
  · intro x hx
    exact ⟨V.wellFormed x,hno x hx⟩

end ContinuumCoulomb

end

end OAI
