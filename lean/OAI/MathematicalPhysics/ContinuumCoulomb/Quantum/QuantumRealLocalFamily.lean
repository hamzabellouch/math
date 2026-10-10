import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoordinateSpectrum

namespace OAI

/-! A real Hermitian six-local circuit Hamiltonian, with explicit linear
term count and the proved complete Hilbert-space promise gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaRebitOnQubits_zero {ι : Type*} :
    qmaRebitOnQubits (0 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) = 0 := by
  ext s t
  simp [qmaRebitOnQubits,qmaRebitMatrix]

theorem qmaRebitOnQubits_sum {ι κ : Type*} [Fintype κ]
    (A : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    qmaRebitOnQubits (∑ i, A i) = ∑ i, qmaRebitOnQubits (A i) := by
  have hs (s : Finset κ) : qmaRebitOnQubits (∑ i ∈ s, A i) =
      ∑ i ∈ s, qmaRebitOnQubits (A i) := by
    induction s using Finset.induction_on with
    | empty => simp [qmaRebitOnQubits_zero]
    | @insert a s ha ih => simp only [Finset.sum_insert ha,qmaRebitOnQubits_add,ih]
  exact hs Finset.univ

theorem qmaRebitOnQubits_hermitian {ι : Type*}
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : A.IsHermitian) :
    (qmaRebitOnQubits A).IsHermitian :=
  (qmaRebitMatrix_hermitian A hA).submatrix (fun s : Unit ⊕ ι → Fin 2 => (s (Sum.inl ()),s ∘ Sum.inr))

def qmaRealCircuitTermSites (c : QMACircuit) (i : QMACircuitTerm c) :=
  qmaRebitSites (qmaCircuitTermSites c i)

def qmaRealCircuitTermMatrix (c : QMACircuit) (i : QMACircuitTerm c) :=
  qmaRebitOnQubits (qmaCircuitTermMatrix c i)

theorem qmaRealCircuitTerm_local (c : QMACircuit) (i : QMACircuitTerm c) :
    QMALocalOn (qmaRealCircuitTermSites c i) (qmaRealCircuitTermMatrix c i) :=
  qmaRebitOnQubits_local (qmaCircuitTerm_local c i)

theorem qmaRealCircuitTerm_support_card (c : QMACircuit) (i : QMACircuitTerm c) :
    (qmaRealCircuitTermSites c i).card ≤ 6 := by
  have h := qmaCircuitTerm_support_card c i
  change (qmaRebitSites (qmaCircuitTermSites c i)).card ≤ 6
  rw [qmaRebitSites_card]
  omega

theorem qmaRealCircuitTerm_hermitian (c : QMACircuit) (i : QMACircuitTerm c) :
    (qmaRealCircuitTermMatrix c i).IsHermitian :=
  qmaRebitOnQubits_hermitian _ (qmaCircuitTerm_hermitian c i)

theorem qmaRealCircuitTerm_real (c : QMACircuit) (i : QMACircuitTerm c)
    (s t : Unit ⊕ QMACircuitQubit c → Fin 2) :
    (qmaRealCircuitTermMatrix c i s t).im = 0 := qmaRebitMatrix_real _ _ _

theorem qmaRealCircuitTerm_sum (c : QMACircuit) :
    (∑ i : QMACircuitTerm c, qmaRealCircuitTermMatrix c i) = qmaRealQubitHamiltonian c := by
  change (∑ i, qmaRebitOnQubits (qmaCircuitTermMatrix c i)) = _
  rw [←qmaRebitOnQubits_sum,qmaCircuitTerm_sum]
  rfl

theorem qmaRealCircuitTerm_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (Unit ⊕ QMACircuitQubit c → Fin 2)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (∑ i, qmaRealCircuitTermMatrix c i) (fun p => u p) := by
  rw [qmaRealCircuitTerm_sum]
  exact qmaRealQubitHamiltonian_sound c hc hsound u

theorem qmaRealCircuitQubit_card (c : QMACircuit) :
    Fintype.card (Unit ⊕ QMACircuitQubit c) = c.gates.length+c.work+4 := by
  simp only [QMACircuitQubit,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
  omega

theorem qmaRealCircuitTerm_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (Unit ⊕ QMACircuitQubit c → Fin 2), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (∑ i, qmaRealCircuitTermMatrix c i)
        (fun p => u p) ≤ 1 := by
  rw [qmaRealCircuitTerm_sum]
  exact qmaRealQubitHamiltonian_accepting c hc psi hpsi hacc

end ContinuumCoulomb

end

end OAI
