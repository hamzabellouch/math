import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceRetained
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSamplePair
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSampleUnits
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSurvivorRows
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeightReindex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def reindexedCanonicalPairTerm (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (χ:PrimeCharacterData (schedule k j) width Q)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (s v w:ℤ) (tL tR:HistoryReconstruction.Tree j) : ℂ :=
  let HL:=copiedSampleState (schedule k j) j width hL
  let HR:=copiedSampleState (schedule k j) j width hR
  let Y:=outsideSampleState (schedule k j) j width y
  let q:=reconstructedPivot k j (pairedState k j HL HR Y) s v w
  if hp:0<q then
    if s≠0 ∧ positivePivotOfPos q hp∈R j ∧ s*q=v*(∏i,HR i)-w*(∏i,HL i) then
      RetainedRow.term k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W (positivePivotOfPos q hp) HL Y (v,tL)
        (sampledRetainedPhase k j hj width χ a hL y (positivePivotOfPos q hp) v tL) *
      conj (RetainedRow.term k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W (positivePivotOfPos q hp) HR Y (w,tR)
        (sampledRetainedPhase k j hj width χ a hR y (positivePivotOfPos q hp) w tR))
    else 0
  else 0

theorem reindexedCanonicalPairTerm_eq (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (χ:PrimeCharacterData (schedule k j) width Q) (hχ:∀i p,χ i p≠1)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (s v w:ℤ) (tL tR:HistoryReconstruction.Tree j)
    (ht:∀i,HistoryFrequencyUnits (nextSample (schedule k j) j width hL hR y i).val
      (j+1) s ((v,w),tL,tR))
    (hlarge:∀i,∀q:ℕ,Nat.Prime q → q∣(pairedState k j
      (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y) i).natAbs → s.natAbs<q)
    (hPB:∀P∈R j,(P:ℤ)≤B j (pairedState k j
      (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y)))
    (hv:|v|≤V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)))
    (hw:|w|≤V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)))
    (hgap:2*B j (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y))*
      V j (pairedState k j (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y))<
      ∏i,copiedSampleState (schedule k j) j width hR i) :
    reindexedCanonicalPairTerm k j hj width χ a B V R leafMask X Δ W hL hR y s v w tL tR =
      if samplePrimeSupport (schedule k (j+1)) width (nextSample (schedule k j) j width hL hR y) then
        retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
          X Δ W (j+1) s (pairedState k j (copiedSampleState (schedule k j) j width hL)
            (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y))
          ((v,w),tL,tR) *
        sampledHistoryPhase k (j+1) width
          (fun i => χ (previousConstituent (schedule k j) j width i))
          (fun i => a (previousConstituent (schedule k j) j width i))
          (nextSample (schedule k j) j width hL hR y) s ((v,w),tL,tR)
      else 0 := by
  let HL:=copiedSampleState (schedule k j) j width hL
  let HR:=copiedSampleState (schedule k j) j width hR
  let Y:=outsideSampleState (schedule k j) j width y
  let x:=pairedState k j HL HR Y
  let q:=reconstructedPivot k j x s v w
  let WL:=retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
    X Δ W j v (sourceState k j q HL Y) tL
  let WR:=retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
    X Δ W j w (sourceState k j q HR Y) tR
  let Wn:=retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
    X Δ W (j+1) s x ((v,w),tL,tR)
  let phase:=sampledHistoryPhase k (j+1) width
    (fun i => χ (previousConstituent (schedule k j) j width i))
    (fun i => a (previousConstituent (schedule k j) j width i))
    (nextSample (schedule k j) j width hL hR y) s ((v,w),tL,tR)
  have hweight:=reindexedCanonicalWeight_eq k j hj B V R leafMask X Δ W
    HL HR Y s v w tL tR hlarge hPB hv hw hgap
  change (if hp:0<q then if s≠0 ∧ positivePivotOfPos q hp∈R j ∧
    s*q=v*(∏i,HR i)-w*(∏i,HL i) then WL*conj WR else 0 else 0)=Wn at hweight
  change reindexedCanonicalPairTerm k j hj width χ a B V R leafMask X Δ W hL hR y s v w tL tR =
    if samplePrimeSupport _ _ _ then Wn*phase else 0
  unfold reindexedCanonicalPairTerm
  dsimp only
  by_cases hp:0<q
  · rw [dite_eq_left hp] at hweight ⊢
    by_cases hg:s≠0 ∧ positivePivotOfPos q hp∈R j ∧ s*q=v*(∏i,HR i)-w*(∏i,HL i)
    · rw [ite_eq_left hg] at hweight ⊢
      let P:=positivePivotOfPos q hp
      have hq:(P:ℤ)=q:=Int.toNat_of_nonneg hp.le
      have hterms : RetainedRow.term k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
          X Δ W P HL Y (v,tL) (sampledRetainedPhase k j hj width χ a hL y P v tL) *
        conj (RetainedRow.term k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
          X Δ W P HR Y (w,tR) (sampledRetainedPhase k j hj width χ a hR y P w tR)) =
        (WL*conj WR)*(sampledRetainedPhase k j hj width χ a hL y P v tL *
          conj (sampledRetainedPhase k j hj width χ a hR y P w tR)) := by
        simp only [RetainedRow.term,hq,map_mul]
        change (WL*_)*(conj WR*_)=(WL*conj WR)*_; ring
      rw [hterms]
      by_cases hl0:WL=0
      · have hn:Wn=0:=by rw [←hweight,hl0,zero_mul]
        simp only [hl0,zero_mul,hn,ite_self]
      by_cases hr0:WR=0
      · have hn:Wn=0:=by rw [←hweight,hr0,map_zero,mul_zero]
        simp only [hr0,map_zero,mul_zero,zero_mul,hn,ite_self]
      have hl:= (retainedHistoryWeight_support hl0).current
      have hr:= (retainedHistoryWeight_support hr0).current
      have hn:=hl.paired_of_reversal_prime_factors hj hr hg.1 hg.2.2.symm hlarge
      have hlP:CurrentAtomSupport k j v (sourceState k j (P:ℤ) HL Y):=by simpa only [hq] using hl
      have hrP:CurrentAtomSupport k j w (sourceState k j (P:ℤ) HR Y):=by simpa only [hq] using hr
      by_cases hi:copiedWithinAtomPrimeSupport (schedule k j) j width hL ∧
        copiedWithinAtomPrimeSupport (schedule k j) j width hR ∧
        outsideWithinAtomPrimeSupport (schedule k j) j width y
      · have hc:=nextSample_primeSupport_of_current width hn hi.1 hi.2.1 hi.2.2
        rw [ite_eq_left hc]
        simp only [sampledRetainedPhase,hi.1,hi.2.1,hi.2.2,and_self,ite_true]
        have hrev:s*(P:ℤ)=v*((∏i,(hR i).val:ℕ):ℤ)-w*((∏i,(hL i).val:ℕ):ℤ):=by
          simpa only [hq,HL,HR,prod_copiedSampleState] using hg.2.2
        rw [sampledPivotSurviving_pair k j hj width χ hχ a hL hR y P s ((v,w),tL,tR)
          hc ht hrev (sampled_pivot_units_of_source_support hj width hlP hrP),hweight]
      · have hc:¬samplePrimeSupport (schedule k (j+1)) width (nextSample (schedule k j) j width hL hR y):=by
          intro hc
          exact hi ((nextSample_prime_support_iff k j width hL hR y).mp hc).2
        rw [ite_eq_right hc]
        have hz:sampledRetainedPhase k j hj width χ a hL y P v tL *
            conj (sampledRetainedPhase k j hj width χ a hR y P w tR)=0:=by
          unfold sampledRetainedPhase
          split_ifs with hleft hright
          · exact False.elim (hi ⟨hleft.1,hright.1,hleft.2⟩)
          · simp only [map_zero,mul_zero]
          · simp only [zero_mul]
          · simp only [zero_mul]
        rw [hz,mul_zero]
    · rw [ite_eq_right hg] at hweight ⊢
      rw [←hweight]
      simp only [zero_mul,ite_self]
  · rw [dite_eq_right hp] at hweight ⊢
    rw [←hweight]
    simp only [zero_mul,ite_self]

end Ostmann.Characters.Template

end

end OAI
