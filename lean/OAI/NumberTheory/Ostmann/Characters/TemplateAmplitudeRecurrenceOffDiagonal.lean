import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceBounds
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceFrequencySupport
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceShellPair

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem unitOffDiagonal_eq_nextAmplitude (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (E:(schedule k j).Constituent width→Finset (PrimeUpTo Q))
    (hE:∀i,0<primeShellMass (E i))
    (ζ:PrimeUnitData (schedule k j) width Q) (hζ:∀i p,‖ζ i p‖=1)
    (χ:PrimeCharacterData (schedule k j) width Q) (hχ:∀i p,p∈E i→χ i p≠1)
    (a:PrimeTranslationData (schedule k j) width Q)
    (B V:(j:ℕ)→State k (j+1)→ℤ) (R:ℕ→Finset ℕ+)
    (leafMask:ℤ→State k 0→Prop) (X Δ W:ℝ)
    (S:List Bool→Finset ℤ) (T:Finset ℤ) (U:ℕ)
    (hU:∀i p,p∈E i→U<p.val)
    (hF:∀path f,f∈stepHistoryRanges S T path→f≠0 ∧ f.natAbs≤U)
    (hBounds:∀y,(outsidePrimePrior (schedule k j) j width E hE).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width E hE).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width E hE).mass hR≠0→
      ∀z z':SupportedHistory S j [],canonicalPairBounds k j width B V R leafMask X Δ W
        hL hR y z.val.1 z'.val.1 z.val.2 z'.val.2)
    (hcut:∀y,(outsidePrimePrior (schedule k j) j width E hE).mass y≠0→
      ∀hL hR,(copiedPrimePrior (schedule k j) j width E hE).mass hL≠0→
      (copiedPrimePrior (schedule k j) j width E hE).mass hR≠0→
      ∀(z z':SupportedHistory S j []),∀P∈R j,∀s:ℤ,
      z.val.1*(∏i,copiedSampleState (schedule k j) j width hR i)-
        z'.val.1*(∏i,copiedSampleState (schedule k j) j width hL i)≠0→
      z.val.1*(∏i,copiedSampleState (schedule k j) j width hR i)-
        z'.val.1*(∏i,copiedSampleState (schedule k j) j width hL i)=s*(P:ℤ)→
      RetainedRow.pairCoefficient k j B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width)
        S [] (fun y P h z=>unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2)
        y hL hR z z' P≠0→s∈T) :
    unitOffDiagonal k j hj width E hE ζ χ a B V (canonicalHistoryExtra k R)
      (canonicalHistoryMask k leafMask) X Δ W S (R j) =
    unitAmplitude k (j+1) width (nextUnitData (schedule k j) j width ζ)
      (fun i=>χ (previousConstituent (schedule k j) j width i))
      (fun i=>a (previousConstituent (schedule k j) j width i))
      B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask) X Δ W
      (stepHistoryRanges S T) (nextPrimeShells (schedule k j) j width E)
      (nextPrimeShells_positive (schedule k j) j width E hE) := by
  have hprod (h:CopiedConstituent (schedule k j) j width→PrimeUpTo Q) :
      (∏i,copiedSampleState (schedule k j) j width h i)≠0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro b hb
    exact_mod_cast (primeUpTo_prime (h ⟨i,b⟩)).pos
  unfold unitOffDiagonal
  rw [RetainedRow.offDiagonal_frequency_sum_support _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj hprod T hcut]
  unfold unitAmplitude
  rw [next_constituentPrimePrior_cmean (schedule k j) j width E hE]
  apply FinitePrior.cmean_congr_support
  intro y hy
  apply FinitePrior.cmean_congr_support
  intro hL hLm
  apply FinitePrior.cmean_congr_support
  intro hR hRm
  let xn:=nextSample (schedule k j) j width hL hR y
  let xp:=pairedState k j (copiedSampleState (schedule k j) j width hL)
    (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)
  let φ:=fun s t=>if samplePrimeSupport (schedule k (j+1)) width xn then
    retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
      X Δ W (j+1) s xp t *
    unitHistoryPhase k (j+1) width (nextUnitData (schedule k j) j width ζ)
      (fun i=>χ (previousConstituent (schedule k j) j width i))
      (fun i=>a (previousConstituent (schedule k j) j width i)) xn s t else 0
  have hmass : (constituentPrimePrior (schedule k (j+1)) width (nextPrimeShells (schedule k j) j width E)
      (nextPrimeShells_positive (schedule k j) j width E hE)).mass xn≠0 := by
    rw [next_constituentPrimePrior_mass (schedule k j) j width E hE]
    exact mul_ne_zero (mul_ne_zero hy hLm) hRm
  have hNextU : ∀i p,p∈nextPrimeShells (schedule k j) j width E i→U<p.val := by
    intro i p hp
    rw [nextPrimeShells_eq_previous] at hp
    exact hU _ p hp
  have hchar (i:(schedule k (j+1)).Constituent width) :
      χ (previousConstituent (schedule k j) j width i) (xn i)≠1 := by
    apply hχ
    have hh := primeProductPrior_mem_of_mass_ne_zero (nextPrimeShells (schedule k j) j width E)
      (nextPrimeShells_positive (schedule k j) j width E hE) xn hmass i
    simpa only [nextPrimeShells_eq_previous] using hh
  have hp (z z':SupportedHistory S j []) (s:ℤ) (hs:s∈T) :
      RetainedRow.frequencyPairCoefficient k j B V (canonicalHistoryExtra k R)
        (canonicalHistoryMask k leafMask) X Δ W
        (copiedSampleState (schedule k j) j width) (outsideSampleState (schedule k j) j width)
        S [] (R j) (fun y P h z=>unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2)
        T y hL hR z z' s = φ s ((z.val.1,z'.val.1),z.val.2,z'.val.2) := by
    let zn:SupportedHistory (stepHistoryRanges S T) (j+1) [] :=
      (stepHistoryEquiv S T j).symm (⟨s,hs⟩,z,z')
    have ht := constituentPrimePrior_historyFrequencyUnits (schedule k (j+1)) width
      (nextPrimeShells (schedule k j) j width E)
      (nextPrimeShells_positive (schedule k j) j width E hE) hNextU xn hmass
      (stepHistoryRanges S T) hF [] zn
    rw [frequencyPairCoefficient_eq_unitPairTerm]
    exact reindexedCanonicalUnitPairTerm_eq_of_sample_support k j hj width ζ hζ χ a B V R leafMask
      X Δ W hL hR y s z.val.1 z'.val.1 z.val.2 z'.val.2 hchar ht
      (pairedSampleState_prime_factor_gt k j width E hE hU hL hR y hLm hRm hy s
        (hF [] s (by simpa only [stepHistoryRanges_nil] using hs)).2)
      (hBounds y hy hL hR hLm hRm z z')
  calc
    _ = ∑z:SupportedHistory S j [],∑z':SupportedHistory S j [],∑s∈T,
        φ s ((z.val.1,z'.val.1),z.val.2,z'.val.2) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro z' hz'
      exact Finset.sum_congr rfl (fun s hs=>hp z z' s hs)
    _ = ∑z:SupportedHistory (stepHistoryRanges S T) (j+1) [],φ z.val.1 z.val.2 := by
      rw [sum_oldHistories_root,←sum_stepHistory]
    _ = _ := by
      rw [unitAmplitudeIntegrand_eq]
      simp only [φ,Finset.sum_ite_irrel,Finset.sum_const_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      rw [constituentSampleState_nextSample]

end Ostmann.Characters.Template

end

end OAI
