import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalDecomposition

namespace OAI

/-! A linear-size explicit interaction family for the verified circuit
Hamiltonian. Its supports contain at most five qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMACircuitTerm (c : QMACircuit) :=
  Fin (c.gates.length+1) ⊕ (Fin 2 ⊕ (Fin (c.work+1) ⊕ (Unit ⊕ Fin c.gates.length)))

def qmaCircuitTermSites (c : QMACircuit) : QMACircuitTerm c → Finset (QMACircuitQubit c)
  | .inl i => {Sum.inl i.castSucc,Sum.inl i.succ}
  | .inr (.inl b) => if b = 0 then {Sum.inl 0} else {Sum.inl (Fin.last (c.gates.length+1))}
  | .inr (.inr (.inl i)) => {Sum.inl (qmaInputMarker c),Sum.inr i}
  | .inr (.inr (.inr (.inl _))) => {Sum.inl (qmaOutputMarker c),Sum.inr (Fin.last c.work)}
  | .inr (.inr (.inr (.inr t))) => qmaPropagationSites c t

def qmaCircuitTermMatrix (c : QMACircuit) : QMACircuitTerm c →
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ
  | .inl i => qmaClockFaultTerm c i
  | .inr (.inl b) => if b = 0 then qmaClockLeftTerm c else qmaClockRightTerm c
  | .inr (.inr (.inl i)) => qmaInputTerm c i
  | .inr (.inr (.inr (.inl _))) => qmaOutputTerm c
  | .inr (.inr (.inr (.inr t))) =>
    (8*c.gates.length:ℂ) • ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t)

theorem qmaCircuitTerm_card (c : QMACircuit) :
    Fintype.card (QMACircuitTerm c) = 2*c.gates.length+c.work+5 := by
  simp only [QMACircuitTerm,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  omega

theorem qmaCircuitTerm_local (c : QMACircuit) (i : QMACircuitTerm c) :
    QMALocalOn (qmaCircuitTermSites c i) (qmaCircuitTermMatrix c i) := by
  rcases i with i | (b | (i | (u | t)))
  · exact qmaClockFaultTerm_local c i
  · fin_cases b
    · exact qmaClockLeftTerm_local c
    · exact qmaClockRightTerm_local c
  · exact qmaInputTerm_local c i
  · exact qmaOutputTerm_local c
  · exact (qmaLocalPropagationGram_local c t).smul _

theorem qmaCircuitTerm_support_card (c : QMACircuit) (i : QMACircuitTerm c) :
    (qmaCircuitTermSites c i).card ≤ 5 := by
  have hp (a b : QMACircuitQubit c) : ({a,b} : Finset (QMACircuitQubit c)).card ≤ 2 := by
    have h := Finset.card_insert_le a ({b} : Finset (QMACircuitQubit c))
    simpa only [Finset.card_singleton] using h
  rcases i with i | (b | (i | (u | t)))
  · exact le_trans (hp _ _) (by norm_num : (2:ℕ) ≤ 5)
  · fin_cases b <;> simp [qmaCircuitTermSites]
  · exact le_trans (hp _ _) (by norm_num : (2:ℕ) ≤ 5)
  · exact le_trans (hp _ _) (by norm_num : (2:ℕ) ≤ 5)
  · exact qmaPropagationSites_card c t

theorem qmaCircuitTerm_sum (c : QMACircuit) :
    (∑ i : QMACircuitTerm c, qmaCircuitTermMatrix c i) = qmaQubitHamiltonian c := by
  rw [qmaQubitHamiltonian_decomposition]
  have h10 : (1:Fin 2) ≠ 0 := by decide
  simp only [Fintype.sum_sum_type,qmaCircuitTermMatrix,Fin.sum_univ_two,
    Fin.isValue,ite_true,h10,ite_false,Finset.univ_unique,Finset.sum_singleton,
    ←Finset.smul_sum]
  ext s t
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem qmaCircuitTerm_hermitian (c : QMACircuit) (i : QMACircuitTerm c) :
    (qmaCircuitTermMatrix c i).IsHermitian := by
  have hd (f : (QMACircuitQubit c → Fin 2) → ℂ)
      (hf : ∀ s, star (f s) = f s) : (Matrix.diagonal f).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    exact hf s
  rcases i with i | (b | (i | (u | t)))
  · apply hd
    intro s
    dsimp only
    split_ifs <;> simp
  · fin_cases b <;> apply hd <;> intro s <;> dsimp only <;> split_ifs <;> simp
  · apply hd
    intro s
    dsimp only
    split_ifs <;> simp
  · apply hd
    intro s
    dsimp only
    split_ifs <;> simp
  · exact (Matrix.isHermitian_conjTranspose_mul_self _).smul (by simp [isSelfAdjoint_iff])

end ContinuumCoulomb

end

end OAI
