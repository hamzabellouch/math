import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitExpectation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries PivotProductFibers PivotEliminationActual HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) (R : Finset ℕ+)

def unitDiagonal : ℝ :=
  RetainedRow.diagonal k j B V extra mask X Δ W
    (copiedPrimePrior (schedule k j) j width E hE) (outsidePrimePrior (schedule k j) j width E hE)
    (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width) S [] R
    (fun y P h z => unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2)

def unitOffDiagonal : ℂ :=
  RetainedRow.offDiagonal k j B V extra mask X Δ W
    (copiedPrimePrior (schedule k j) j width E hE) (outsidePrimePrior (schedule k j) j width E hE)
    (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width) S [] R
    (fun y P h z => unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2)

theorem unitAmplitude_sq_le_diagonal_offDiagonal
    (hζ : ∀i p,‖ζ i p‖=1) (hχ : ∀i p,p∈E i→χ i p≠1) (U:ℕ)
    (hU : ∀i p,p∈E i → U<p.val)
    (hS : ∀path f,f∈S path → f≠0 ∧ f.natAbs≤U)
    (hR : ∀w : PrimeTuple Q (width ((schedule k j).role (pivotSlot k j hj).val)),
      (∀i,w i∈E ⟨(pivotSlot k j hj).val,i⟩) → positiveTupleProduct w∈R) :
    ‖unitAmplitude k j width ζ χ a B V extra mask X Δ W S E hE‖^2 ≤
      (((width ((schedule k j).role (pivotSlot k j hj).val)).factorial:ℝ)*
        PivotProductFibers.normalization (fun i => E ⟨(pivotSlot k j hj).val,i⟩))*
      (unitDiagonal k j hj width E hE ζ χ a B V extra mask X Δ W S R+
        ‖unitOffDiagonal k j hj width E hE ζ χ a B V extra mask X Δ W S R‖) := by
  rw [unitAmplitude_eq_extracted k j hj width E hE ζ χ a B V extra mask X Δ W S hχ U hU hS]
  apply (unitExtractedAmplitude_sq_le_energy k j hj width E hE ζ χ a B V extra mask X Δ W S
    hζ hχ R hR).trans
  apply mul_le_mul_of_nonneg_left
  · apply RetainedRow.energy_le_diagonal_add_norm k j B V extra mask X Δ W
      (copiedPrimePrior (schedule k j) j width E hE) (outsidePrimePrior (schedule k j) j width E hE)
      (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width) S [] R _ hj
    intro h
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro b hb
    exact_mod_cast (primeUpTo_prime (h ⟨i,b⟩)).pos
  · exact mul_nonneg (Nat.cast_nonneg _) (normalization_nonneg _ (fun i => hE _))

end
end Ostmann.Characters.Template

end

end OAI
