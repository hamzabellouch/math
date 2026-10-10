import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingMatching
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSampleDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HistoryFrequencyLabels
open DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem survivingSample_mem_of_mass (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hh : (copiedPrimePrior (schedule k j) j width E hE).mass h≠0)
    (hy : (outsidePrimePrior (schedule k j) j width E hE).mass y≠0)
    (i : SurvivingPrimeIndex k j width) :
    Sum.elim h y i ∈ E (scheduledConstituentInput k j hj width (.inr i)) := by
  cases i with
  | inl i =>
    exact primeProductPrior_mem_of_mass_ne_zero
      (fun i=>E (copiedConstituentOld (schedule k j) j width i))
      (fun i=>hE (copiedConstituentOld (schedule k j) j width i)) h hh i
  | inr i =>
    exact primeProductPrior_mem_of_mass_ne_zero
      (fun i=>E (outsideConstituentOld (schedule k j) j width i))
      (fun i=>hE (outsideConstituentOld (schedule k j) j width i)) y hy i

theorem finiteSurvivingCharacters_order_of_mass (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (hχ : ∀i p,p∈E i → 2<orderOf (χ i p))
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hh : (copiedPrimePrior (schedule k j) j width E hE).mass h≠0)
    (hy : (outsidePrimePrior (schedule k j) j width E hE).mass y≠0)
    (i : SurvivingPrimeIndex k j width) :
    2<orderOf (finiteSurvivingCharacters k j hj width χ i (Sum.elim h y i).val) := by
  rw [finiteSurvivingCharacters,extendCharacterData_prime]
  exact hχ _ _ (survivingSample_mem_of_mass k j hj width E hE h y hh hy i)

theorem finiteSurvivingUnits_norm (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀i p,‖ζ i p‖=1)
    (i : SurvivingPrimeIndex k j width) (q : ℕ) :
    ‖finiteSurvivingUnits k j hj width ζ i q‖=1 :=
  norm_extendUnitData _ (fun _i p=>hζ _ p) i q

theorem survivingHistoryUnits_of_mass (k j : ℕ) (width : Role→ℕ) {Q V : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (hV : ∀i p,p∈E i → V<p.val)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hh : (copiedPrimePrior (schedule k j) j width E hE).mass h≠0)
    (hy : (outsidePrimePrior (schedule k j) j width E hE).mass y≠0)
    (ranges : List Bool→Finset ℤ)
    (hrange : ∀path f,f∈ranges path → f≠0 ∧ f.natAbs≤V)
    (path : List Bool) (t : SupportedHistory ranges j path) (i : SurvivingPrimeIndex k j width) :
    HistoryFrequencyUnits (Sum.elim h y i).val j t.val.1 t.val.2 := by
  cases i with
  | inl i => exact copiedPrimePrior_historyFrequencyUnits _ _ _ E hE hV h hh ranges hrange path t i
  | inr i => exact outsidePrimePrior_historyFrequencyUnits _ _ _ E hE hV y hy ranges hrange path t i

theorem changed_actualCode_surviving_squarePhase_of_original_prior {k Q V : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : ∀i,IsCopiedBulk cfg m j (σ i) ↔ IsCopiedBulk cfg m j i)
    (hρ : ∀i,IsCopiedBulk cfg m j (ρ i) ↔ IsCopiedBulk cfg m j i)
    (hcode : ¬∀i,actualCopiedCode cfg m j (σ i)=actualCopiedCode cfg m j (ρ i))
    (E : (schedule k j).Constituent (sourceWidth cfg m) → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (hV : ∀i p,p∈E i → V<p.val)
    (χ : PrimeCharacterData (schedule k j) (sourceWidth cfg m) Q)
    (hχ : ∀i p,p∈E i → 2<orderOf (χ i p))
    (a : PrimeTranslationData (schedule k j) (sourceWidth cfg m) Q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) Q) (hζ : ∀i p,‖ζ i p‖=1)
    (h : ActualCopied cfg m j → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hh : (copiedPrimePrior (schedule k j) j (sourceWidth cfg m) E hE).mass h≠0)
    (hy : (outsidePrimePrior (schedule k j) j (sourceWidth cfg m) E hE).mass y≠0)
    (hc : Pairwise (fun i h'=>(Sum.elim h y i).val.Coprime (Sum.elim h y h').val))
    (ranges : List Bool→Finset ℤ)
    (hrange : ∀path f,f∈ranges path → f≠0 ∧ f.natAbs≤V)
    (t u : SupportedHistory ranges j []) (hroot : t.val.1=u.val.1) (P : ℕ) :
    let : ∀i : SurvivingPrimeIndex k j (sourceWidth cfg m),Fact (Sum.elim h y i).val.Prime :=
      fun i=>⟨primeUpTo_prime (Sum.elim h y i)⟩
    ∃z : Word k j × Fin m, ∃a₀ : Fin j, ∃b : Bool,
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) (fun i=>(Sum.elim h y i).val)
        (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χ)
        (finiteSurvivingTranslations k j hj (sourceWidth cfg m) a)
        (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) P t.val.1 t.val.2 u.val.2
        (.inl (copiedBulk cfg m j z)) (.inr (copiedRetiredOutside cfg m j hj.le false a₀ b)) ∨
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) (fun i=>(Sum.elim h y i).val)
        (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χ)
        (finiteSurvivingTranslations k j hj (sourceWidth cfg m) a)
        (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) P t.val.1 t.val.2 u.val.2
        (.inr (copiedRetiredOutside cfg m j hj.le true a₀ b)) (.inl (copiedBulk cfg m j z)) := by
  let : ∀i : SurvivingPrimeIndex k j (sourceWidth cfg m),Fact (Sum.elim h y i).val.Prime :=
    fun i=>⟨primeUpTo_prime (Sum.elim h y i)⟩
  refine changed_actualCode_surviving_squarePhase cfg m j hj σ ρ hσ hρ hcode _ hc
    (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χ) ?_
    (finiteSurvivingTranslations k j hj (sourceWidth cfg m) a)
    (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) ?_ P t.val.1 t.val.2 u.val.2 ?_ ?_
  · exact finiteSurvivingCharacters_order_of_mass k j hj (sourceWidth cfg m) E hE χ hχ h y hh hy
  · intro i q
    exact (finiteSurvivingUnits_norm k j hj (sourceWidth cfg m) ζ hζ i q).le
  · exact survivingHistoryUnits_of_mass k j (sourceWidth cfg m) E hE hV h y hh hy ranges hrange [] t
  · rw [hroot]
    exact survivingHistoryUnits_of_mass k j (sourceWidth cfg m) E hE hV h y hh hy ranges hrange [] u

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
