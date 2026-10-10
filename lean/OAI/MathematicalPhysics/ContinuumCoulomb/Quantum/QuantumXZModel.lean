import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZFamily
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitTwoLocal

namespace OAI

/-! A finite X/Z Hamiltonian and its application to the actual verifier circuit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem QMARealLocalModel.toXZ (M : QMARealLocalModel 2) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMAXZModel, |G.energy-M.energy| ≤ 1/N ∧
      G.qubits ≤ M.qubits+80*M.terms ∧ G.terms ≤ 448*M.terms := by
  let E := QMALocalEvenPauliTerm M.sites
  obtain ⟨v,K,hy,hv,he⟩ := qmaTwoLocalXZ_exists
    (fun p : E => qmaLocalPauliWord M.sites p.val)
    (fun p : E => qmaLocalPauliCoefficient M.matrix M.sites p.val)
    (qmaLocalEvenPauli_support M.sites M.card) (qmaLocalEvenPauli_even M.sites) hN
  let G := QMAXZModel.ofWords v K hy hv
  have hs : (∑ p : E, (qmaLocalPauliCoefficient M.matrix M.sites p.val:ℂ) •
      qmaPauliWord (qmaLocalPauliWord M.sites p.val)) = ∑ a, M.matrix a :=
    qmaLocalEvenPauli_sum M.matrix M.sites M.localOn M.hermitian M.real
  have hc : Fintype.card E ≤ 16*M.terms := qmaLocalEvenPauli_count M.sites M.card
  refine ⟨G,?_,?_,?_⟩
  · change |(QMAXZModel.ofWords v K hy hv).energy-M.energy| ≤ 1/N
    rw [QMAXZModel.ofWords_energy,QMARealLocalModel.energy,← hs]
    convert he using 1
    congr 2
    exact qmaNormalizedBottom_instances _ _ _ _ _
  · change Fintype.card ((M.Q ⊕ E) ⊕ (E × Fin 4)) ≤ M.qubits+80*M.terms
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    change M.qubits+Fintype.card E+Fintype.card E*4 ≤ _
    omega
  · change Fintype.card ((E × Fin 4) × Fin 7) ≤ 448*M.terms
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega

theorem qmaCircuit_XZ (c : QMACircuit) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMAXZModel,
      |G.energy-MediatorGraph.normalizedBottom (qmaRealQubitHamiltonian c)| ≤ 1/N ∧
      G.qubits ≤ c.gates.length+c.work+4+602373361664*(2*c.gates.length+c.work+5) ∧
      G.terms ≤ 3367254360064*(2*c.gates.length+c.work+5) := by
  have h2N : 1 ≤ 2*N := by linarith
  obtain ⟨M,he₁,hq₁,ht₁⟩ := qmaCircuit_two_local c h2N
  obtain ⟨G,he₂,hq₂,ht₂⟩ := M.toXZ h2N
  refine ⟨G,?_,?_,?_⟩
  · apply (abs_sub_le G.energy M.energy _).trans
    apply (add_le_add he₂ he₁).trans
    have h : 1/(2*N)+1/(2*N) = 1/N := by ring
    exact h.le
  · omega
  · omega

end ContinuumCoulomb

end

end OAI
