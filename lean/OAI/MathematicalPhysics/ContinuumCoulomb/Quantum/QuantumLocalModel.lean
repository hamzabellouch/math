import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalThird

namespace OAI

/-! Finite real local families and the three gadget stages used by the
circuit-to-spin reduction. This records mathematical families, not a compiler. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

structure QMARealLocalModel (d : ℕ) where
  Q : Type
  Term : Type
  [qFinite : Fintype Q]
  [qDecidable : DecidableEq Q]
  [termFinite : Fintype Term]
  matrix : Term → Matrix (Q → Fin 2) (Q → Fin 2) ℂ
  sites : Term → Finset Q
  localOn : ∀ a, QMALocalOn (sites a) (matrix a)
  card : ∀ a, (sites a).card ≤ d
  hermitian : ∀ a, (matrix a).IsHermitian
  real : ∀ a, QMAEntryParity false (matrix a)

attribute [instance] QMARealLocalModel.qFinite QMARealLocalModel.qDecidable QMARealLocalModel.termFinite

def QMARealLocalModel.energy {d : ℕ} (M : QMARealLocalModel d) : ℝ :=
  MediatorGraph.normalizedBottom (∑ a, M.matrix a)

def QMARealLocalModel.qubits {d : ℕ} (M : QMARealLocalModel d) : ℕ := Fintype.card M.Q

def QMARealLocalModel.terms {d : ℕ} (M : QMARealLocalModel d) : ℕ := Fintype.card M.Term

theorem QMARealLocalModel.subdivision {d : ℕ} (M : QMARealLocalModel (2*d)) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMARealLocalModel (d+1), |G.energy-M.energy| ≤ 1/N ∧
      G.qubits ≤ M.qubits+4^(2*d)*M.terms ∧ G.terms ≤ 4*4^(2*d)*M.terms := by
  obtain ⟨G,hGH,hGR,hGS,hGE⟩ := qmaLocalSubdivision_exists M.matrix M.sites M.card
    M.localOn M.hermitian M.real hN
  choose S hScard hSlocal using hGS
  refine ⟨⟨M.Q ⊕ QMALocalEvenPauliTerm M.sites,QMALocalEvenPauliTerm M.sites × Fin 4,
    G,S,hSlocal,hScard,hGH,hGR⟩,hGE,?_⟩
  exact qmaLocalSubdivision_size M.sites M.card

theorem QMARealLocalModel.third (M : QMARealLocalModel 3) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMARealLocalModel 2, |G.energy-M.energy| ≤ 1/N ∧
      G.qubits ≤ M.qubits+64*M.terms ∧ G.terms ≤ 448*M.terms := by
  obtain ⟨G,hGH,hGR,hGS,hGE⟩ := qmaLocalThird_exists M.matrix M.sites M.card
    M.localOn M.hermitian M.real hN
  choose S hScard hSlocal using hGS
  refine ⟨⟨M.Q ⊕ QMALocalEvenPauliTerm M.sites,QMALocalEvenPauliTerm M.sites × Fin 7,
    G,S,hSlocal,hScard,hGH,hGR⟩,hGE,?_⟩
  exact qmaLocalThird_size M.sites M.card

theorem QMARealLocalModel.six_to_two (M : QMARealLocalModel 6) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMARealLocalModel 2, |G.energy-M.energy| ≤ 1/N ∧
      G.qubits ≤ M.qubits+1077940224*M.terms ∧ G.terms ≤ 7516192768*M.terms := by
  have h3N : 1 ≤ 3*N := by linarith
  obtain ⟨M4,h4,hq4,ht4⟩ := M.subdivision (d := 3) h3N
  obtain ⟨M3,h3,hq3,ht3⟩ := M4.subdivision (d := 2) h3N
  obtain ⟨M2,h2,hq2,ht2⟩ := M3.third h3N
  refine ⟨M2,?_,?_,?_⟩
  · have ht := (abs_sub_le M2.energy M3.energy M.energy).trans
      (add_le_add le_rfl (abs_sub_le M3.energy M4.energy M.energy))
    have hN0 : N ≠ 0 := by linarith
    have he : 1/(3*N)+1/(3*N)+1/(3*N) = 1/N := by field_simp; ring
    linarith
  · norm_num only [show (4:ℕ)^6 = 4096 by norm_num,show (4:ℕ)^4 = 256 by norm_num] at hq4 ht4 hq3 ht3
    omega
  · norm_num only [show (4:ℕ)^6 = 4096 by norm_num,show (4:ℕ)^4 = 256 by norm_num] at ht4 ht3
    omega

end ContinuumCoulomb

end

end OAI
