import OAI.NumberTheory.Ostmann.Characters.TemplateActualPivotFactors

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem actualHistoryPhase_pivot_split (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (p:(schedule k j).Constituent width→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i h => (p i).Coprime (p h)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (hχ:∀i,χ i≠1)
    (a:∀i,ZMod (p i)) (s:ℤ) (t:HistoryReconstruction.Tree j)
    (ht:∀i,HistoryFrequencyUnits (p i) j s t) :
    let e := scheduledConstituentInput k j hj width
    let p' := fun i => p (e i)
    let hc' : Pairwise (fun i h => (p' i).Coprime (p' h)) :=
      fun _ _ h => hc (fun he => h (e.injective he))
    actualHistoryPhase k j width p χ a s t =
      actualPivotOutgoing k j hj width (fun i => p' (.inl i))
        (fun i => χ (e (.inl i))) (fun i => a (e (.inl i))) (inputOutsideProduct p')
        (groupedPivotResidue (fun i => p' (.inl i)) (inputCopiedProduct p')
          (copiedProduct_coprime_pivot p' hc') s)*
      actualPivotSurviving k j hj width (fun i => p' (.inr i))
        (fun i => χ (e (.inr i))) (fun i => a (e (.inr i))) (∏i,p' (.inl i)) s t := by
  classical
  let e := scheduledConstituentInput k j hj width
  let p' := fun i => p (e i)
  let hc' : Pairwise (fun i h => (p' i).Coprime (p' h)) :=
    fun _ _ h => hc (fun he => h (e.injective he))
  let ν := fun i => actualHistoryUnary k width (χ i) j s t i
  let κ := fun i:PivotPrimeIndex k j hj width =>
    historyRegularKappa k width (χ (e (.inl i)))
      (fun _ => initialKappa (χ (e (.inl i)))) j (e (.inl i))
  let bP := fun i:SurvivingPrimeIndex k j width =>
    collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
      (graph k j) (intraGraph k j) (some i) none
  have hr (i:PivotPrimeIndex k j hj width) :
      (schedule k j).IsRegular j (e (.inl i)).1 := by
    change (schedule k j).IsRegular j (pivotSlot k j hj).val
    exact scheduled_pivot_regular k j hj
  have hs (i:PivotPrimeIndex k j hj width) : rowSign k j (e (.inl i)).1=1 := by
    change rowSign k j (pivotSlot k j hj).val=1
    exact pivotSlot_rowSign k j hj
  have hν (i:PivotPrimeIndex k j hj width) :
      ν (e (.inl i))=κ i*χ (e (.inl i)) (s:ZMod (p' (.inl i)))^(-(1:ℤ)) := by
    have hh := actualHistoryUnary_regular k width (χ (e (.inl i))) (hχ _) j
      (Nat.le_of_lt hj) s t (ht _) (e (.inl i)) (hr i)
    simpa only [hs,Units.val_one] using hh
  have hself (i:PivotPrimeIndex k j hj width) :
      constituentGraph k j width (e (.inl i)) (e (.inl i))=0 := by
    simp [constituentGraph,liftGraph]
  have hreg (i:PivotPrimeIndex k j hj width) (z) (hz:z≠Sum.inl i) :
      constituentGraph k j width (e (.inl i)) (e z)=1 := by
    have hh := constituentGraph_regular k j (Nat.le_of_lt hj) width (e (.inl i))
      (hr i) (e z) (fun he => hz (e.injective he))
    simpa only [hs,Units.val_one] using hh
  have hcol (i:SurvivingPrimeIndex k j width) (z:PivotPrimeIndex k j hj width) :
      constituentGraph k j width (e (.inr i)) (e (.inl z))=bP i :=
    scheduledInput_pivot_column k j hj width i z
  have hsplit := complete_phase_pivot_split p' hc' (fun i => χ (e i)) (fun i => a (e i))
    (fun i => ν (e i)) (fun i h => constituentGraph k j width (e i) (e h))
    κ (fun _ => 1) bP s hν hself hreg hcol
  have hreindex := completePrimePhase_reindex e p χ a ν (constituentGraph k j width) s
  exact hreindex.symm.trans hsplit

end Ostmann.Characters.Template

end

end OAI
