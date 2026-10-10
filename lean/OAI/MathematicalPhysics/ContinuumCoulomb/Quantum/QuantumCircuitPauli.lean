import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalCore
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliParity

namespace OAI

/-! An explicit polynomial-size Pauli family for the actual real circuit
Hamiltonian. Every nonzero coefficient has even Y parity. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMACircuitPauliTerm (c : QMACircuit) :=
  (i : QMACircuitTerm c) × ({x // x ∈ qmaRealCircuitTermSites c i} → Fin 4)

def qmaCircuitPauliCoefficient (c : QMACircuit) (p : QMACircuitPauliTerm c) : ℝ :=
  (qmaPauliCoefficient (qmaLocalCore (qmaRealCircuitTermSites c p.1)
    (qmaRealCircuitTermMatrix c p.1)) p.2).re

def qmaCircuitPauliMatrix (c : QMACircuit) (p : QMACircuitPauliTerm c) :
    Matrix (Unit ⊕ QMACircuitQubit c → Fin 2) (Unit ⊕ QMACircuitQubit c → Fin 2) ℂ :=
  (qmaCircuitPauliCoefficient c p : ℂ) •
    qmaLocalLift (qmaRealCircuitTermSites c p.1) (qmaPauliWord p.2)

theorem qmaCircuitPauli_sum (c : QMACircuit) :
    (∑ p : QMACircuitPauliTerm c, qmaCircuitPauliMatrix c p) = qmaRealQubitHamiltonian c := by
  rw [Fintype.sum_sigma]
  have he (i : QMACircuitTerm c) : (∑ w : {x // x ∈ qmaRealCircuitTermSites c i} → Fin 4,
      qmaCircuitPauliMatrix c ⟨i,w⟩) = qmaRealCircuitTermMatrix c i :=
    (qmaRealCircuitTerm_local c i).pauli_expansion (qmaRealCircuitTerm_hermitian c i)
  simp_rw [he]
  exact qmaRealCircuitTerm_sum c

theorem qmaCircuitPauli_count (c : QMACircuit) :
    Fintype.card (QMACircuitPauliTerm c) ≤ 4096*(2*c.gates.length+c.work+5) := by
  calc
    _ = ∑ i : QMACircuitTerm c, 4^(qmaRealCircuitTermSites c i).card := by
      simp only [QMACircuitPauliTerm,Fintype.card_sigma,Fintype.card_fun,
        Fintype.card_fin,Fintype.card_coe]
    _ ≤ ∑ _i : QMACircuitTerm c, 4096 := by
      apply Finset.sum_le_sum
      intro i _
      have h := qmaRealCircuitTerm_support_card c i
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 4) h
      exact hp.trans (by norm_num)
    _ = _ := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul,Finset.card_univ,qmaCircuitTerm_card]
      exact Nat.mul_comm _ _

theorem qmaCircuitPauli_odd_zero (c : QMACircuit) (p : QMACircuitPauliTerm c)
    (hp : Odd (qmaPauliYCount p.2)) : qmaCircuitPauliCoefficient c p = 0 := by
  have hH := qmaLocalCore_hermitian (qmaRealCircuitTermSites c p.1)
    (qmaRealCircuitTermMatrix c p.1) (qmaRealCircuitTerm_hermitian c p.1)
  have hR := qmaLocalCore_real (qmaRealCircuitTermSites c p.1)
    (qmaRealCircuitTermMatrix c p.1) (qmaRealCircuitTerm_real c p.1)
  exact congrArg Complex.re (qmaPauliCoefficient_odd_zero _ hH hR p.2 hp)

theorem qmaCircuitPauli_support (c : QMACircuit) (p : QMACircuitPauliTerm c) :
    QMALocalOn (qmaRealCircuitTermSites c p.1) (qmaCircuitPauliMatrix c p) := by
  apply QMALocalOn.smul
  exact ⟨qmaPauliWord p.2,rfl⟩

end ContinuumCoulomb

end

end OAI
