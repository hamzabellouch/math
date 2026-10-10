import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalPauli

namespace OAI

/-! A real three-local family reduces to a real two-local family, with
seven output terms per even Pauli word and the actual spectral error. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem qmaLocalThird_exists (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) (hS : ∀ a, (S a).card ≤ 3)
    (hF : ∀ a, QMALocalOn (S a) (F a)) (hH : ∀ a, (F a).IsHermitian)
    (hR : ∀ a, QMAEntryParity false (F a)) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : (QMALocalEvenPauliTerm S × Fin 7) →
        Matrix (ι ⊕ QMALocalEvenPauliTerm S → Fin 2) (ι ⊕ QMALocalEvenPauliTerm S → Fin 2) ℂ,
      (∀ p, (G p).IsHermitian) ∧ (∀ p, QMAEntryParity false (G p)) ∧
      (∀ p, ∃ T : Finset (ι ⊕ QMALocalEvenPauliTerm S), T.card ≤ 2 ∧ QMALocalOn T (G p)) ∧
      |MediatorGraph.normalizedBottom (∑ p, G p)-MediatorGraph.normalizedBottom (∑ a, F a)| ≤ 1/N := by
  obtain ⟨G,hGH,hGR,hGS,hGE⟩ := qmaPauliThird_exists
    (fun p : QMALocalEvenPauliTerm S => qmaLocalPauliWord S p.val)
    (fun p => qmaLocalPauliCoefficient F S p.val)
    (qmaLocalEvenPauli_support S hS) (qmaLocalEvenPauli_even S) hN
  refine ⟨G,hGH,hGR,hGS,?_⟩
  have hs : (∑ p : QMALocalEvenPauliTerm S,
      (qmaLocalPauliCoefficient F S p.val : ℂ) • qmaPauliWord (qmaLocalPauliWord S p.val)) =
        ∑ a, F a := qmaLocalEvenPauli_sum F S hF hH hR
  rwa [hs] at hGE

theorem qmaLocalThird_size (S : α → Finset ι) (hS : ∀ a, (S a).card ≤ 3) :
    Fintype.card (ι ⊕ QMALocalEvenPauliTerm S) ≤ Fintype.card ι+64*Fintype.card α ∧
    Fintype.card (QMALocalEvenPauliTerm S × Fin 7) ≤ 448*Fintype.card α := by
  have hc := qmaLocalEvenPauli_count S hS
  norm_num only [show (4:ℕ)^3 = 64 by norm_num] at hc
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  constructor <;> omega

end ContinuumCoulomb

end

end OAI
