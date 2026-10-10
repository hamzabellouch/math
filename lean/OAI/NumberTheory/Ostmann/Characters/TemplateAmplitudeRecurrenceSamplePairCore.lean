import OAI.NumberTheory.Ostmann.Characters.TemplateActualPhasePair
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSamplePairMaps

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable
local instance {Q:ℕ} (p:PrimeUpTo Q) : Fact p.val.Prime := ⟨primeUpTo_prime p⟩

theorem sampledPivotSurviving_pair_core (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (χ:PrimeCharacterData (schedule k j) width Q) (hχ:∀i p,χ i p≠1)
    (a:PrimeTranslationData (schedule k j) width Q)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (P:ℕ+) (s:ℤ) (t:HistoryReconstruction.Tree (j+1))
    (hc:samplePrimeSupport (schedule k (j+1)) width
      (nextSample (schedule k j) j width hL hR y))
    (ht:∀i,HistoryFrequencyUnits (nextSample (schedule k j) j width hL hR y i).val (j+1) s t)
    (he:s*(P:ℤ)=t.1.1*((∏i,(hR i).val:ℕ):ℤ)-t.1.2*((∏i,(hL i).val:ℕ):ℤ))
    (hP:∀i,(P:ZMod (nextSample (schedule k j) j width hL hR y i).val)≠0) :
    actualPivotSurviving k j hj width (fun i => (Sum.elim hL y i).val)
      (fun i => χ (scheduledConstituentInput k j hj width (.inr i)) (Sum.elim hL y i))
      (fun i => a (scheduledConstituentInput k j hj width (.inr i)) (Sum.elim hL y i))
      P t.1.1 t.2.1 *
      conj (actualPivotSurviving k j hj width (fun i => (Sum.elim hR y i).val)
        (fun i => χ (scheduledConstituentInput k j hj width (.inr i)) (Sum.elim hR y i))
        (fun i => a (scheduledConstituentInput k j hj width (.inr i)) (Sum.elim hR y i))
        P t.1.2 t.2.2) =
    sampledHistoryPhase k (j+1) width
      (fun i => χ (previousConstituent (schedule k j) j width i))
      (fun i => a (previousConstituent (schedule k j) j width i))
      (nextSample (schedule k j) j width hL hR y) s t := by
  let e := nextConstituentEquiv (schedule k j) j width
  let z : UnaryOutputIndex k j width→PrimeUpTo Q :=
    Sum.elim (fun ib => if ib.2 then hL ib.1 else hR ib.1) y
  let p := fun i => (z i).val
  let old : UnaryOutputIndex k j width→(schedule k j).Constituent width :=
    Sum.elim (fun ib => copiedConstituentOld (schedule k j) j width ib.1)
      (outsideConstituentOld (schedule k j) j width)
  let χ' := fun i => χ (old i) (z i)
  let a' := fun i => a (old i) (z i)
  let : ∀i,Fact (p i).Prime := fun i => ⟨primeUpTo_prime (z i)⟩
  have hz (i:UnaryOutputIndex k j width) :
      nextSample (schedule k j) j width hL hR y (e.symm i)=z i := by
    exact nextSample_output k j width hL hR y i
  have hnext (i:(schedule k (j+1)).Constituent width) :
      nextSample (schedule k j) j width hL hR y i=z (e i) := by
    simpa only [Equiv.symm_apply_apply] using hz (e i)
  have hc' : Pairwise (fun i h => (p i).Coprime (p h)) := by
    intro i h hih
    have hh := hc (fun he => hih (e.symm.injective he))
    simpa only [hz] using hh
  have ht' (i) : HistoryFrequencyUnits (p i) (j+1) s t := by
    simpa only [hz] using ht (e.symm i)
  have hP' (i) : ((P:ℕ):ZMod (p i))≠0 := by
    have hi := hP (e.symm i)
    change (fun q:PrimeUpTo Q => ((P:ℕ):ZMod q.val)≠0)
      (nextSample (schedule k j) j width hL hR y (e.symm i)) at hi
    rw [hz] at hi
    exact hi
  have he' : s*((P:ℕ):ℤ)=t.1.1*(primeCopyProduct p false:ℤ)-t.1.2*(primeCopyProduct p true:ℤ) := by
    simpa only [primeCopyProduct,p,z,Sum.elim_inl,Bool.false_eq_true,ite_false,ite_true] using he
  have hh := actualPivotSurviving_pair k j hj width p hc' χ' (fun i => hχ _ _) a'
    (P:ℕ) s t ht' he' hP'
  have hzL (i:SurvivingPrimeIndex k j width) :
      z (survivingBranchIndex true i)=Sum.elim hL y i := by cases i <;> rfl
  have hzR (i:SurvivingPrimeIndex k j width) :
      z (survivingBranchIndex false i)=Sum.elim hR y i := by cases i <;> rfl
  have hold (side:Bool) (i:SurvivingPrimeIndex k j width) :
      old (survivingBranchIndex side i)=scheduledConstituentInput k j hj width (.inr i) := by
    cases i <;> rfl
  have hprev (i:(schedule k (j+1)).Constituent width) :
      old (e i)=previousConstituent (schedule k j) j width i := by
    change Sum.elim _ _ (e i)=_
    unfold previousConstituent
    rcases heq:e i with ⟨h,b⟩ | y
    · rfl
    · rfl
  dsimp only [p,χ',a'] at hh
  simp only [hold] at hh
  let F (zz:SurvivingPrimeIndex k j width→PrimeUpTo Q)
      (v:ℤ) (tt:HistoryReconstruction.Tree j) : ℂ :=
    actualPivotSurviving k j hj width (fun i => (zz i).val)
      (fun i => χ (scheduledConstituentInput k j hj width (.inr i)) (zz i))
      (fun i => a (scheduledConstituentInput k j hj width (.inr i)) (zz i)) P v tt
  have hleft : F (fun i => z (survivingBranchIndex true i)) t.1.1 t.2.1 =
      F (Sum.elim hL y) t.1.1 t.2.1 :=
    congrArg (fun zz => F zz t.1.1 t.2.1) (funext hzL)
  have hright : F (fun i => z (survivingBranchIndex false i)) t.1.2 t.2.2 =
      F (Sum.elim hR y) t.1.2 t.2.2 :=
    congrArg (fun zz => F zz t.1.2 t.2.2) (funext hzR)
  change F (fun i => z (survivingBranchIndex true i)) t.1.1 t.2.1 *
      conj (F (fun i => z (survivingBranchIndex false i)) t.1.2 t.2.2) = _ at hh
  rw [hleft,hright] at hh
  have holdnext : (fun i => old (e i)) = previousConstituent (schedule k j) j width :=
    funext hprev
  change F (Sum.elim hL y) t.1.1 t.2.1 * conj (F (Sum.elim hR y) t.1.2 t.2.2) =
    sampledHistoryPhase k (j+1) width (fun i => χ (old (e i)))
      (fun i => a (old (e i))) (fun i => z (e i)) s t at hh
  have hdata : (fun i => χ (old (e i))) =
      (fun i => χ (previousConstituent (schedule k j) j width i)) := by
    funext i; rw [hprev]
  have hadata : (fun i => a (old (e i))) =
      (fun i => a (previousConstituent (schedule k j) j width i)) := by
    funext i; rw [hprev]
  rw [hdata,hadata,← funext hnext] at hh
  exact hh

end Ostmann.Characters.Template

end

end OAI
