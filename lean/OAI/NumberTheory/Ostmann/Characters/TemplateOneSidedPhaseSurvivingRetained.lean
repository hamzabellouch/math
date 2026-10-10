import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingRetainedDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HistoryFrequencyLabels
open DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

theorem source_changed_actualCode_retained_squarePhase {k Q V : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : ∀i,IsCopiedBulk cfg m j (σ i) ↔ IsCopiedBulk cfg m j i)
    (hρ : ∀i,IsCopiedBulk cfg m j (ρ i) ↔ IsCopiedBulk cfg m j i)
    (hcode : ¬∀i,actualCopiedCode cfg m j (σ i)=actualCopiedCode cfg m j (ρ i))
    (E : (schedule k j).Constituent (sourceWidth cfg m) → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (hV : ∀i p,p∈E i → V<p.val)
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (hχ : ∀i p,p∈E i → 2<orderOf
      (scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j i p))
    (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) Q) (hζ : ∀i p,‖ζ i p‖=1)
    (h : ActualCopied cfg m j → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j (sourceWidth cfg m) → PrimeUpTo Q)
    (hh : (copiedPrimePrior (schedule k j) j (sourceWidth cfg m) E hE).mass h≠0)
    (hy : (outsidePrimePrior (schedule k j) j (sourceWidth cfg m) E hE).mass y≠0)
    (hc : Pairwise (fun i h'=>(Sum.elim h y i).val.Coprime (Sum.elim h y h').val))
    (ranges : List Bool→Finset ℤ)
    (hrange : ∀path f,f∈ranges path → f≠0 ∧ f.natAbs≤V)
    (t u : SupportedHistory ranges j []) (hroot : t.val.1=u.val.1) (P : ℕ+) :
    let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j
    let ad := scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j
    ∃z : Word k j × Fin m, ∃a₀ : Fin j, ∃b : Bool,
      RetainedSquarePhase k j hj (sourceWidth cfg m) σ ρ χd ad ζ h y P t.val.1 t.val.2 u.val.2
        (.inl (copiedBulk cfg m j z)) (.inr (copiedRetiredOutside cfg m j hj.le false a₀ b)) ∨
      RetainedSquarePhase k j hj (sourceWidth cfg m) σ ρ χd ad ζ h y P t.val.1 t.val.2 u.val.2
        (.inr (copiedRetiredOutside cfg m j hj.le true a₀ b)) (.inl (copiedBulk cfg m j z)) := by
  let : ∀i : SurvivingPrimeIndex k j (sourceWidth cfg m),Fact (Sum.elim h y i).val.Prime :=
    fun i=>⟨primeUpTo_prime (Sum.elim h y i)⟩
  obtain ⟨z,a₀,b,hp | hp⟩ := changed_actualCode_surviving_squarePhase_of_original_prior cfg m j hj
    σ ρ hσ hρ hcode E hE hV
    (scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j) hχ
    (scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j)
    ζ hζ h y hh hy hc ranges hrange t u hroot P
  · refine ⟨z,a₀,b,Or.inl ?_⟩
    exact (source_retainedSquarePhase_iff cfg m j hj ζ χ a σ ρ h y hc P t.val.1 t.val.2 u.val.2 _ _).mpr hp
  · refine ⟨z,a₀,b,Or.inr ?_⟩
    exact (source_retainedSquarePhase_iff cfg m j hj ζ χ a σ ρ h y hc P t.val.1 t.val.2 u.val.2 _ _).mpr hp

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
