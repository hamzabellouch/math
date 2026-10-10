import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalModel

namespace OAI

/-! The actual unary-clock circuit matrix admits a polynomial-size real
2-local approximation with an explicit finite interaction family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaCircuitLocalModel (c : QMACircuit) : QMARealLocalModel 6 where
  Q := Unit ⊕ QMACircuitQubit c
  Term := QMACircuitTerm c
  qFinite := inferInstance
  qDecidable := inferInstance
  termFinite := inferInstance
  matrix := qmaRealCircuitTermMatrix c
  sites := qmaRealCircuitTermSites c
  localOn := qmaRealCircuitTerm_local c
  card := qmaRealCircuitTerm_support_card c
  hermitian := qmaRealCircuitTerm_hermitian c
  real := qmaRealCircuitTerm_real c

theorem qmaCircuitLocalModel_energy (c : QMACircuit) :
    (qmaCircuitLocalModel c).energy = MediatorGraph.normalizedBottom (qmaRealQubitHamiltonian c) := by
  change MediatorGraph.normalizedBottom (∑ i, qmaRealCircuitTermMatrix c i) = _
  rw [qmaRealCircuitTerm_sum]

theorem qmaCircuitLocalModel_size (c : QMACircuit) :
    (qmaCircuitLocalModel c).qubits = c.gates.length+c.work+4 ∧
    (qmaCircuitLocalModel c).terms = 2*c.gates.length+c.work+5 :=
  ⟨qmaRealCircuitQubit_card c,qmaCircuitTerm_card c⟩

theorem qmaCircuitLocalModel_yes (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    (qmaCircuitLocalModel c).energy ≤ 1/(3*(c.gates.length+1:ℝ)) := by
  obtain ⟨u,hu,he⟩ := qmaRealQubitHamiltonian_accepting c hc psi hpsi hacc
  rw [qmaCircuitLocalModel_energy]
  apply (qmaNormalizedBottom_le _ u hu).trans
  apply (le_div_iff₀ (by positivity : 0 < 3*(c.gates.length+1:ℝ))).mpr
  linarith

theorem qmaCircuitLocalModel_no (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) :
    2/(5*(c.gates.length+1:ℝ)) ≤ (qmaCircuitLocalModel c).energy := by
  rw [qmaCircuitLocalModel_energy]
  apply le_qmaNormalizedBottom _ (EuclideanSpace.single (fun _ => (0:Fin 2)) (1:ℂ))
    (by simp [PiLp.norm_single])
  intro u hu
  have hs := qmaRealQubitHamiltonian_sound c hc hsound u
  rw [hu,one_pow,mul_one] at hs
  apply (div_le_iff₀ (by positivity : 0 < 5*(c.gates.length+1:ℝ))).mpr
  linarith

theorem qmaCircuit_two_local (c : QMACircuit) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMARealLocalModel 2,
      |G.energy-MediatorGraph.normalizedBottom (qmaRealQubitHamiltonian c)| ≤ 1/N ∧
      G.qubits ≤ c.gates.length+c.work+4+1077940224*(2*c.gates.length+c.work+5) ∧
      G.terms ≤ 7516192768*(2*c.gates.length+c.work+5) := by
  obtain ⟨G,hG,hQ,hT⟩ := (qmaCircuitLocalModel c).six_to_two hN
  rw [qmaCircuitLocalModel_energy] at hG
  rw [(qmaCircuitLocalModel_size c).1,(qmaCircuitLocalModel_size c).2] at hQ
  rw [(qmaCircuitLocalModel_size c).2] at hT
  exact ⟨G,hG,hQ,hT⟩

end ContinuumCoulomb

end

end OAI
