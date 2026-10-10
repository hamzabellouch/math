import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSamplePairMaps
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagationBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem CurrentAtomSupport.outside_pivot_coprime {k j:ℕ} (hj:j<k) {P s:ℤ}
    {h:CopiedState k j} {y:OutsideState k j}
    (hs:CurrentAtomSupport k j s (sourceState k j P h y))
    (i:{i:(schedule k j).Slot // (schedule k j).IsOutside j i}) : IsCoprime (y i) P := by
  have hne:i.val≠(pivotSlot k j hj).val := by
    intro he
    exact i.property.1 (he ▸ (pivotSlot k j hj).property)
  have hh := hs.pairwise hne
  change IsCoprime (sourceState k j P h y i.val)
    (sourceState k j P h y (pivotSlot k j hj).val) at hh
  rw [sourceState_outside_value] at hh
  simpa only [sourceState,childState_pivot k j true _ _ _ (pivotSlot k j hj).property] using hh

theorem copiedSample_pivot_coprime {k j:ℕ} (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    {P:ℕ+} {s:ℤ}
    {h:CopiedConstituent (schedule k j) j width→PrimeUpTo Q}
    {y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q}
    (hs:CurrentAtomSupport k j s (sourceState k j (P:ℤ)
      (copiedSampleState (schedule k j) j width h)
      (outsideSampleState (schedule k j) j width y)))
    (i:CopiedConstituent (schedule k j) j width) : (h i).val.Coprime P := by
  have hh := hs.copied_pivot_coprime hj i.1
  have hd:((h i).val:ℤ)∣copiedSampleState (schedule k j) j width h i.1 :=
    Finset.dvd_prod_of_mem (fun a => ((h ⟨i.1,a⟩).val:ℤ)) (Finset.mem_univ i.2)
  have hp := hh.of_isCoprime_of_dvd_left hd
  simpa only [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast] using hp

theorem outsideSample_pivot_coprime {k j:ℕ} (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    {P:ℕ+} {s:ℤ}
    {h:CopiedConstituent (schedule k j) j width→PrimeUpTo Q}
    {y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q}
    (hs:CurrentAtomSupport k j s (sourceState k j (P:ℤ)
      (copiedSampleState (schedule k j) j width h)
      (outsideSampleState (schedule k j) j width y)))
    (i:OutsideConstituent (schedule k j) j width) : (y i).val.Coprime P := by
  have hh := hs.outside_pivot_coprime hj i.1
  have hd:((y i).val:ℤ)∣outsideSampleState (schedule k j) j width y i.1 :=
    Finset.dvd_prod_of_mem (fun a => ((y ⟨i.1,a⟩).val:ℤ)) (Finset.mem_univ i.2)
  have hp := hh.of_isCoprime_of_dvd_left hd
  simpa only [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast] using hp

theorem sampled_pivot_units_of_source_support {k j:ℕ} (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    {P:ℕ+} {v w:ℤ}
    {hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q}
    {y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q}
    (hl:CurrentAtomSupport k j v (sourceState k j (P:ℤ)
      (copiedSampleState (schedule k j) j width hL)
      (outsideSampleState (schedule k j) j width y)))
    (hr:CurrentAtomSupport k j w (sourceState k j (P:ℤ)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y))) :
    ∀i,(P:ZMod (nextSample (schedule k j) j width hL hR y i).val)≠0 := by
  intro i
  have hp:(nextSample (schedule k j) j width hL hR y i).val.Coprime P := by
    rw [nextSample_output_apply]
    rcases nextConstituentEquiv (schedule k j) j width i with ⟨h,b⟩ | yy
    · cases b
      · exact copiedSample_pivot_coprime hj width hr h
      · exact copiedSample_pivot_coprime hj width hl h
    · exact outsideSample_pivot_coprime hj width hl yy
  intro he
  exact ((primeUpTo_prime _).coprime_iff_not_dvd.mp hp) ((ZMod.natCast_eq_zero_iff _ _).mp he)

theorem nextSample_primeSupport_of_current {k j:ℕ} (width:Role→ℕ) {Q:ℕ} {s:ℤ}
    {hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q}
    {y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q}
    (hs:CurrentAtomSupport k (j+1) s (pairedState k j
      (copiedSampleState (schedule k j) j width hL)
      (copiedSampleState (schedule k j) j width hR)
      (outsideSampleState (schedule k j) j width y)))
    (hl:copiedWithinAtomPrimeSupport (schedule k j) j width hL)
    (hr:copiedWithinAtomPrimeSupport (schedule k j) j width hR)
    (hy:outsideWithinAtomPrimeSupport (schedule k j) j width y) :
    samplePrimeSupport (schedule k (j+1)) width (nextSample (schedule k j) j width hL hR y) :=
  (nextSample_prime_support_iff k j width hL hR y).mpr ⟨hs.pairwise,hl,hr,hy⟩

end Ostmann.Characters.Template

end

end OAI
