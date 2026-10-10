import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSupportedSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalPauli

namespace OAI

/-! Each real local family admits the actual simultaneous subdivision step. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem qmaLocalSubdivision_supported (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : α → Finset ι) {d : ℕ} (hS : ∀ a, (S a).card ≤ 2*d)
    (hF : ∀ a, QMALocalOn (S a) (F a)) (hH : ∀ a, (F a).IsHermitian)
    (hR : ∀ a, QMAEntryParity false (F a)) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : (QMALocalEvenPauliTerm S × Fin 4) →
        Matrix (ι ⊕ QMALocalEvenPauliTerm S → Fin 2) (ι ⊕ QMALocalEvenPauliTerm S → Fin 2) ℂ,
      (∀ p, (G p).IsHermitian) ∧ (∀ p, QMAEntryParity false (G p)) ∧
      (∀ p, ∃ T : Finset (ι ⊕ QMALocalEvenPauliTerm S), T.card ≤ d+1 ∧ QMALocalOn T (G p) ∧
        T ⊆ qmaMediatorSupport (S p.1.val.1) p.1) ∧
      |MediatorGraph.normalizedBottom (∑ p, G p)-MediatorGraph.normalizedBottom (∑ a, F a)| ≤ 1/N := by
  obtain ⟨G,hGH,hGR,hGS,hGE⟩ := qmaPauliSubdivision_supported
    (fun p : QMALocalEvenPauliTerm S => qmaLocalPauliWord S p.val)
    (fun p => qmaLocalPauliCoefficient F S p.val)
    (qmaLocalEvenPauli_support S hS) (qmaLocalEvenPauli_even S) hN
  refine ⟨G,hGH,hGR,?_,?_⟩
  · intro p
    obtain ⟨T,hTc,hTl,hTs⟩ := hGS p
    exact ⟨T,hTc,hTl,hTs.trans (qmaMediatorSupport_mono (qmaPauliExtend_support _ _) _)⟩
  · have hs : (∑ p : QMALocalEvenPauliTerm S,
        (qmaLocalPauliCoefficient F S p.val : ℂ) • qmaPauliWord (qmaLocalPauliWord S p.val)) =
          ∑ a, F a := qmaLocalEvenPauli_sum F S hF hH hR
    rwa [hs] at hGE

end ContinuumCoulomb

end

end OAI
