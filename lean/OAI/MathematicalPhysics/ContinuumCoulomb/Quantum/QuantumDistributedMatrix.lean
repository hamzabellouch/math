import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedWitness
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalDecomposition

namespace OAI

/-! The distributed-input history is an actual Hermitian matrix on all unary strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaUnaryDistributedDiagonal (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (p : QMAUnaryBasis c) : ℝ :=
  ∑ i : Fin (c.work+1), if qmaClockAt c.gates.length (τ i) p.1 ∧
    qmaInputCheck c i p.2 then 1 else 0

theorem qmaUnaryDistributedDiagonal_form (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun p => (qmaUnaryDistributedDiagonal c τ p : ℂ))) u =
      qmaUnaryDistributedInput c τ u := by
  rw [qmaQuadratic_diagonal_real]
  simp only [qmaUnaryDistributedDiagonal,Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,
    qmaUnaryDistributedInput]

def qmaUnaryDistributedHamiltonian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) : Matrix (QMAUnaryBasis c) (QMAUnaryBasis c) ℂ :=
  Matrix.diagonal (fun p => (qmaUnaryClockDiagonal c p : ℂ))+
    Matrix.diagonal (fun p => (qmaUnaryOutputDiagonal c p : ℂ))+
    (14:ℂ) • Matrix.diagonal (fun p => (qmaUnaryDistributedDiagonal c τ p : ℂ))+
    ((14*(c.work+1)+8)*c.gates.length:ℂ) •
      ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c)

theorem qmaUnaryDistributedHamiltonian_hermitian (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (qmaUnaryDistributedHamiltonian c τ).IsHermitian := by
  have hd (d : QMAUnaryBasis c → ℝ) : (Matrix.diagonal (fun p => (d p : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    simp [isSelfAdjoint_iff]
  exact (((hd _).add (hd _)).add ((hd _).smul (by simp))).add
    ((Matrix.isHermitian_conjTranspose_mul_self (qmaUnaryPropagationMatrix c)).smul
      (by simp [isSelfAdjoint_iff]))

theorem qmaUnaryDistributedHamiltonian_form (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) u = qmaUnaryDistributedEnergy c τ u := by
  unfold qmaUnaryDistributedHamiltonian
  rw [qmaQuadratic_add,qmaQuadratic_add,qmaQuadratic_add]
  have hs : ((14*(c.work+1)+8)*c.gates.length:ℂ) =
      (((14*(c.work+1)+8)*c.gates.length:ℝ):ℂ) := by push_cast; rfl
  rw [hs,show (14:ℂ) = ((14:ℝ):ℂ) from rfl,qmaQuadratic_smul,qmaQuadratic_smul,
    qmaUnaryDistributedDiagonal_form,qmaQuadratic_diagonal_real,
    qmaQuadratic_diagonal_real,qmaUnaryPropagationMatrix_form]
  simp only [qmaUnaryDistributedEnergy,qmaUnaryClockEnergy,qmaUnaryOutputEnergy,
    qmaUnaryClockDiagonal,qmaUnaryOutputDiagonal,Fintype.sum_prod_type,
    ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.mul_sum]

def qmaDistributedInputSites (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    Finset (QMACircuitQubit c) :=
  {Sum.inl (τ i).castSucc,Sum.inl (τ i).succ,Sum.inr i}

def qmaDistributedInputTerm (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  Matrix.diagonal (fun s => if qmaClockAt c.gates.length (τ i) (s ∘ Sum.inl) ∧
    qmaInputCheck c i (s ∘ Sum.inr) then 14 else 0)

theorem qmaDistributedInputTerm_local (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    QMALocalOn (qmaDistributedInputSites c τ i) (qmaDistributedInputTerm c τ i) := by
  apply qmaLocalOn_diagonal
  intro s r h
  have hl := h (Sum.inl (τ i).castSucc) (by simp [qmaDistributedInputSites])
  have hr := h (Sum.inl (τ i).succ) (by simp [qmaDistributedInputSites])
  have hi := h (Sum.inr i) (by simp [qmaDistributedInputSites])
  apply ite_congr
  · simp only [qmaClockAt,qmaInputCheck,Function.comp_apply,hl,hr,hi]
  · intro _; rfl
  · intro _; rfl

theorem qmaDistributedInputSites_card (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (i : Fin (c.work+1)) :
    (qmaDistributedInputSites c τ i).card = 3 := by
  have ht : (τ i).castSucc ≠ (τ i).succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [qmaDistributedInputSites,ht]

theorem qmaUnaryDistributedInput_reindex (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    ((14:ℂ) • Matrix.diagonal (fun p => (qmaUnaryDistributedDiagonal c τ p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      ∑ i : Fin (c.work+1), qmaDistributedInputTerm c τ i := by
  rw [qmaSubmatrix_smul,Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,qmaDistributedInputTerm,
      Matrix.diagonal_apply_eq,qmaUnaryDistributedDiagonal,Complex.ofReal_sum,Function.comp_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : (qmaCircuitQubitSplit c s).1 = s ∘ Sum.inl := rfl
    have hr : (qmaCircuitQubitSplit c s).2 = s ∘ Sum.inr := rfl
    rw [hs,hr]
    by_cases hp : qmaClockAt c.gates.length (τ i) (s ∘ Sum.inl) ∧
      qmaInputCheck c i (s ∘ Sum.inr)
    · simp [hp]
    · simp [hp]
  · simp [Matrix.smul_apply,h,Matrix.sum_apply,qmaDistributedInputTerm]

end ContinuumCoulomb

end

end OAI
