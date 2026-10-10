import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseAction
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open ParityActions Construction Preliminaries
attribute [local instance] Classical.propDecidable

def SquarePhase (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (a : (q : ℕ) → ZMod q)
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (L S : (schedule k j).Constituent width) : Prop :=
  ∃positive : Bool,
    phasePair k j width σ ρ p χ a s t u =
      longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p L) *
      shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p S) *
        exposedCharacter (χ (p S)) positive (p L) ∧
    ‖longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p L)‖ ≤ 1 ∧
    ‖shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p S)‖ ≤ 1 ∧
    exposedCharacter (χ (p S)) positive≠1

theorem terminal_squarePhase (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0<width (.anchor j false))
    {σ ρ : Reassignments k n (width .word)} (hσρ : σ≠ρ)
    (p : (schedule k (n+1)).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,2<orderOf (χ (p i)))
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree (n+1))
    (ht : ∀i,HistoryFrequencyUnits (p i) (n+1) s t)
    (hu : ∀i,HistoryFrequencyUnits (p i) (n+1) s u) :
    ∃z : BulkSlot k n (width .word),∃j : Fin (n+1),∃b : Bool,
      SquarePhase k (n+1) width (constituentPermutation k n width σ)
        (constituentPermutation k n width ρ) p χ a s t u
        (bulkEmbedding k n width z) (smallAnchorConstituent k n hn width hw j b) := by
  obtain ⟨z,j,b,hLS,hforward,hrev⟩ := distinct_reassignments_constituent_edge k n hn width hw hσρ
  refine ⟨z,j,b,?_⟩
  exact phasePair_square k (n+1) width _ _ p hc χ hχ a s t u ht hu _ _ hLS hforward hrev

theorem terminal_squarePhase_of_original_prior (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0<width (.anchor j false))
    {σ ρ : Reassignments k n (width .word)} (hσρ : σ≠ρ) {Q V : ℕ}
    (E : (schedule k (n+1)).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (hV : ∀i p,p∈E i → V<p.val)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (hχ : ∀i p,p∈E i → 2<orderOf (χ p.val)) (a : (q : ℕ) → ZMod q)
    (x : (schedule k (n+1)).Constituent width → PrimeUpTo Q)
    (hx : (constituentPrimePrior (schedule k (n+1)) width E hE).mass x≠0)
    (hsupport : samplePrimeSupport (schedule k (n+1)) width x)
    (ranges : List Bool → Finset ℤ)
    (hrange : ∀path f,f∈ranges path → f≠0 ∧ f.natAbs ≤ V)
    (t u : HistoryFrequencyLabels.SupportedHistory ranges (n+1) []) (hroot : t.val.1=u.val.1) :
    letI : ∀i,Fact (x i).val.Prime := fun i=>⟨primeUpTo_prime (x i)⟩
    ∃z : BulkSlot k n (width .word),∃j : Fin (n+1),∃b : Bool,
      SquarePhase k (n+1) width (constituentPermutation k n width σ)
        (constituentPermutation k n width ρ) (fun i=>(x i).val) χ a t.val.1 t.val.2 u.val.2
        (bulkEmbedding k n width z) (smallAnchorConstituent k n hn width hw j b) := by
  let : ∀i,Fact (x i).val.Prime := fun i=>⟨primeUpTo_prime (x i)⟩
  refine terminal_squarePhase k n hn width hw hσρ (fun i=>(x i).val) hsupport χ ?_ a
    t.val.1 t.val.2 u.val.2 ?_ ?_
  · intro i
    exact hχ i (x i) (primeProductPrior_mem_of_mass_ne_zero E hE x hx i)
  · intro i
    exact constituentPrimePrior_historyFrequencyUnits (schedule k (n+1)) width E hE hV x hx ranges hrange [] t i
  · intro i
    rw [hroot]
    exact constituentPrimePrior_historyFrequencyUnits (schedule k (n+1)) width E hE hV x hx ranges hrange [] u i

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
