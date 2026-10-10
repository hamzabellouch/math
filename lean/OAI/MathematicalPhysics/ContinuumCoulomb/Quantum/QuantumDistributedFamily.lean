import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedSpectrum
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalFamily

namespace OAI

/-! A linear-size, five-local term family with distributed initialization checks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaDistributedQubitHamiltonian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  (qmaUnaryDistributedHamiltonian c τ).submatrix (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c)

theorem qmaDistributedQubitHamiltonian_decomposition (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    qmaDistributedQubitHamiltonian c τ =
      ((∑ i : Fin (c.gates.length+1), qmaClockFaultTerm c i)+qmaClockLeftTerm c+qmaClockRightTerm c)+
      qmaOutputTerm c+(∑ i : Fin (c.work+1), qmaDistributedInputTerm c τ i)+
      ((14*(c.work+1)+8)*c.gates.length:ℂ) • ∑ t : Fin c.gates.length,
        (qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t := by
  unfold qmaDistributedQubitHamiltonian qmaUnaryDistributedHamiltonian
  simp only [qmaSubmatrix_add]
  rw [qmaUnaryClockDiagonal_reindex,qmaUnaryOutputDiagonal_reindex,
    qmaUnaryDistributedInput_reindex,qmaSubmatrix_smul,qmaUnaryPropagationGram_reindex]

def qmaDistributedTermSites (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : QMACircuitTerm c → Finset (QMACircuitQubit c)
  | .inr (.inr (.inl i)) => qmaDistributedInputSites c τ i
  | t => qmaCircuitTermSites c t

def qmaDistributedTermMatrix (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : QMACircuitTerm c →
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ
  | .inl i => qmaClockFaultTerm c i
  | .inr (.inl b) => if b = 0 then qmaClockLeftTerm c else qmaClockRightTerm c
  | .inr (.inr (.inl i)) => qmaDistributedInputTerm c τ i
  | .inr (.inr (.inr (.inl _))) => qmaOutputTerm c
  | .inr (.inr (.inr (.inr t))) =>
    ((14*(c.work+1)+8)*c.gates.length:ℂ) •
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t)

theorem qmaDistributedTerm_local (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c) :
    QMALocalOn (qmaDistributedTermSites c τ t) (qmaDistributedTermMatrix c τ t) := by
  rcases t with i | (b | (i | (u | t)))
  · exact qmaClockFaultTerm_local c i
  · fin_cases b
    · exact qmaClockLeftTerm_local c
    · exact qmaClockRightTerm_local c
  · exact qmaDistributedInputTerm_local c τ i
  · exact qmaOutputTerm_local c
  · exact (qmaLocalPropagationGram_local c t).smul _

theorem qmaDistributedTerm_support_card (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c) :
    (qmaDistributedTermSites c τ t).card ≤ 5 := by
  rcases t with i | (b | (i | (u | t)))
  · exact qmaCircuitTerm_support_card c (.inl i)
  · exact qmaCircuitTerm_support_card c (.inr (.inl b))
  · change (qmaDistributedInputSites c τ i).card ≤ 5
    rw [qmaDistributedInputSites_card]
    norm_num
  · exact qmaCircuitTerm_support_card c (.inr (.inr (.inr (.inl u))))
  · exact qmaPropagationSites_card c t

theorem qmaDistributedTerm_hermitian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c) :
    (qmaDistributedTermMatrix c τ t).IsHermitian := by
  rcases t with i | (b | (i | (u | t)))
  · exact qmaCircuitTerm_hermitian c (.inl i)
  · exact qmaCircuitTerm_hermitian c (.inr (.inl b))
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    split_ifs <;> simp
  · exact qmaCircuitTerm_hermitian c (.inr (.inr (.inr (.inl u))))
  · exact (Matrix.isHermitian_conjTranspose_mul_self _).smul (by simp [isSelfAdjoint_iff])

theorem qmaDistributedTerm_sum (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (∑ t : QMACircuitTerm c, qmaDistributedTermMatrix c τ t) =
      qmaDistributedQubitHamiltonian c τ := by
  rw [qmaDistributedQubitHamiltonian_decomposition]
  have h10 : (1:Fin 2) ≠ 0 := by decide
  simp only [Fintype.sum_sum_type,qmaDistributedTermMatrix,Fin.sum_univ_two,
    Fin.isValue,ite_true,h10,ite_false,Finset.univ_unique,Finset.sum_singleton,
    ←Finset.smul_sum]
  ext s t
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

end ContinuumCoulomb

end

end OAI
