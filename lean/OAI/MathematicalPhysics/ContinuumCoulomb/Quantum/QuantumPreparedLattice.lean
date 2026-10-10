import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPreparedCircuit

namespace OAI

/-! The specified physical source for every well-formed verifier circuit,
including the empty circuit. Padding preserves the original witness register
and acceptance probability. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial

def preparedSource (c : QMACircuit) (hc : c.WellFormed) : SquareLatticeHeisenberg :=
  source (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c)

theorem preparedSource_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖=1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    realSourceGroundEnergy (preparedSource c hc) ≤ ((preparedSource c hc).lower:ℝ) :=
  source_accepting (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) psi hpsi
    ((qmaNonemptyCircuit_acceptance c hc psi) ▸ hacc)

theorem preparedSource_rejecting (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖=1 → qmaAcceptance c hc psi ≤ 1/3) :
    ((preparedSource c hc).upper:ℝ) ≤ realSourceGroundEnergy (preparedSource c hc) :=
  source_rejecting (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c)
    (by intro psi hpsi; rw [qmaNonemptyCircuit_acceptance c hc psi]; exact hsound psi hpsi)

theorem preparedSource_binary_yes (c : QMACircuit) (hc : c.WellFormed) {k : ℕ}
    (hp : (preparedSource c hc).binary.PolynomialPromise k)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖=1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    (preparedSource c hc).binary ∈ (sourceHeisenbergPromise k).yes :=
  (preparedSource c hc).binary_mem_yes hp (preparedSource_accepting c hc psi hpsi hacc)

theorem preparedSource_binary_no (c : QMACircuit) (hc : c.WellFormed) {k : ℕ}
    (hp : (preparedSource c hc).binary.PolynomialPromise k)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖=1 → qmaAcceptance c hc psi ≤ 1/3) :
    (preparedSource c hc).binary ∈ (sourceHeisenbergPromise k).no :=
  (preparedSource c hc).binary_mem_no hp (preparedSource_rejecting c hc hsound)

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
