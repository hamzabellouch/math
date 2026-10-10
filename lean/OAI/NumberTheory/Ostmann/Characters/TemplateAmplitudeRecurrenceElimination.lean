import OAI.NumberTheory.Ostmann.Characters.PivotEliminationActualMaskedRange
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem history_pivot_elimination {Q n : ℕ} {α γ : Type*} [Fintype α] [Fintype γ]
    (k j : ℕ) (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (μ : FinitePrior α) (ν : FinitePrior γ) (h : α → CopiedState k j)
    (y : γ → OutsideState k j) (S : List Bool → Finset ℤ) (path : List Bool)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (R : Finset ℕ+)
    (keep : PrimeTuple Q n → γ → Prop)
    (hR : ∀w:PrimeTuple Q n,(∀i,w i∈E i) → ∀a,keep w a → positiveTupleProduct w∈R)
    (G : (w:PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w:ℕ) → ℂ)
    (phase : γ → ℕ+ → α → SupportedHistory S j path → ℂ)
    (hG : ∀w,(∀i,w i∈E i) → ∀a,keep w a → ∀u,‖G w a u‖≤1) :
    ‖ν.cmean (fun a => (characterTuplePrior E hE).cmean (fun w =>
      if keep w a then μ.cmean (fun x => ∑z:SupportedHistory S j path,
        G w a (historyRowTag k j (positiveTupleProduct w) (h x) z.val.1)*
          historyRowTerm k j mask X Δ W (positiveTupleProduct w) (h x) (y a)
            z.val (phase a (positiveTupleProduct w) x z)) else 0))‖^2 ≤
      ((n.factorial:ℝ)*PivotProductFibers.normalization E)*ν.mean (fun a =>
        ∑P∈R,∑u,‖historyGroupedRow k j μ h (y a) S path mask X Δ W P (phase a P) u‖^2) := by
  have hh := pivot_elimination_masked_subrange E hE ν R keep hR G
    (fun a P => historyGroupedRow k j μ h (y a) S path mask X Δ W P (phase a P)) hG
  simpa only [historyGroupedRow_pairing] using hh

end Ostmann.Characters.Template

end

end OAI
