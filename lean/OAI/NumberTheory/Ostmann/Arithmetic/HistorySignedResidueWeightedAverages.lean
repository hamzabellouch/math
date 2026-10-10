import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallAverageActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueAverages

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySignedResidueWeightedAverages
open Construction HistorySignedResidues HistoryCRTIntegration HistorySignedResidueFactorization
open HistorySupportReduction HistoryPairPattern HistoryPairRows HistoryFrequencyResidues
open HistoryRepresentativeSourceSeparation HistorySignedSpectatorCRT ResidueHaar
open HistoryCRTProjection

def mixedExtension {A : ℕ} (w : MixedPair A→ℂ) (z : ZMod A×ZMod A) : ℂ :=
  by classical exact if hz : IsUnit z.2 then w (z.1,hz.unit) else 0

@[simp] theorem mixedExtension_coe {A : ℕ} (w : MixedPair A→ℂ) (z : MixedPair A) :
    mixedExtension w (z.1,(z.2:ZMod A))=w z := by
  rw [mixedExtension,dite_eq_left z.2.isUnit]
  congr 1
  apply Prod.ext
  · rfl
  · apply Units.ext
    exact z.2.isUnit.unit_spec

variable (K : ℕ) {l : ℕ} (h k : History l) {V : ℕ → ℕ} {outside : List ℕ}
variable (hs : h.Supported V outside) (ks : k.Supported V outside)
variable (hroot : RootGiantsAgree h k) (hsmall : h.root.small.Perm k.root.small)
variable (hlarge : LargePrimes V h) (klarge : LargePrimes V k)
variable (hu : FrequencyUnits (pairedFrequencyProduct h k) h)
variable (ku : FrequencyUnits (pairedFrequencyProduct h k) k) (hle : l≤K)
variable (had : PairAdmissible h k outside)
variable (hV : ∀i : Occurrences h k,∀j≤l,V j<(slot h k i).value)
variable (g : (q : ℕ) → ZMod q → ℂ)
variable (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
variable [NeZero (pairModulus h k outside)] (M : ℕ) [NeZero M]
variable [NeZero (rootModulus h)] [NeZero outside.prod]
variable [NeZero (frequencyModulus h k (K+2))] [NeZero (representativeModulus h k)]
variable (hd : pairModulus h k outside∣M)
variable (hA : rootModulus h∣M) (hD : outside.prod∣M)
variable (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
variable (hCRT : crtModulus h k outside (K+2)∣M)
include hroot hsmall hlarge klarge hu ku hle had hV hprime hg hA hD hR hB hCRT

theorem mixed_weighted_average_eq_four_blocks (w : MixedPair (rootModulus h)→ℂ) :
    average (fun z : MixedPair M=>w (mixedPairMap hA z)*
      liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M)))=
    average (fun z : MixedPair (rootModulus h)=>w z*rootResidueIndicator h (z.1,z.2))*
    average (fun z : MixedPair outside.prod=>residuePairSpectator g outside outside.prod h k (z.1,z.2))*
    average (fun z : MixedPair (frequencyModulus h k (K+2))=>independentFrequencyResidueIndicator K h k (z.1,z.2))*
    average (fun z : MixedPair (representativeModulus h k)=>primeResidueIndicatorB h k hs ks (z.1,z.2)) := by
  have he : (fun z : MixedPair M=>w (mixedPairMap hA z)*
      liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M)))=
      (fun z : MixedPair M=>
        (mixedExtension w (projectedRingPair hA (z.1,(z.2:ZMod M)))*
          rootResidueIndicator h (projectedRingPair hA (z.1,(z.2:ZMod M))))*
        residuePairSpectator g outside outside.prod h k (projectedRingPair hD (z.1,(z.2:ZMod M)))*
        independentFrequencyResidueIndicator K h k (projectedRingPair hR (z.1,(z.2:ZMod M)))*
        primeResidueIndicatorB h k hs ks (projectedRingPair hB (z.1,(z.2:ZMod M)))) := by
    funext z
    have ha : mixedExtension w (projectedRingPair hA (z.1,(z.2:ZMod M)))=w (mixedPairMap hA z) := by
      rw [←mixedExtension_coe w (mixedPairMap hA z)]
      rfl
    rw [ha,liftedResidueTest_eq_four_blocks K h k hs ks hroot hsmall hlarge klarge
      hu ku hle had hV g hprime hg M hd hA hD hR hB]
    simp only [ringPairReduction,projectedRingPair,mul_assoc]
  rw [he]
  simpa only [mixedExtension_coe] using four_mixed_projected_product_average (rootModulus h) outside.prod
    (frequencyModulus h k (K+2)) (representativeModulus h k)
    (had.2.2.2 (K+2)) hCRT hA hD hR hB
    (fun z=>mixedExtension w z*rootResidueIndicator h z)
    (residuePairSpectator g outside outside.prod h k)
    (independentFrequencyResidueIndicator K h k) (primeResidueIndicatorB h k hs ks)

theorem paired_mixed_weighted_average_eq_four_blocks (w : MixedPair (rootModulus h)→ℂ)
    (hsame : frequencyLeaves ((pairedFrequencyProduct h k)^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h k)^(K+2)) k) :
    average (fun z : MixedPair M=>w (mixedPairMap hA z)*
      liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M)))=
    average (fun z : MixedPair (rootModulus h)=>w z*rootResidueIndicator h (z.1,z.2))*
    average (fun z : MixedPair outside.prod=>residuePairSpectator g outside outside.prod h k (z.1,z.2))*
    average (fun z : MixedPair (frequencyModulus h k (K+2))=>pairedFrequencyResidueIndicator K h k (z.1,z.2))*
    average (fun z : MixedPair (representativeModulus h k)=>primeResidueIndicatorB h k hs ks (z.1,z.2)) := by
  have he : (fun z : MixedPair M=>w (mixedPairMap hA z)*
      liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M)))=
      (fun z : MixedPair M=>
        (mixedExtension w (projectedRingPair hA (z.1,(z.2:ZMod M)))*
          rootResidueIndicator h (projectedRingPair hA (z.1,(z.2:ZMod M))))*
        residuePairSpectator g outside outside.prod h k (projectedRingPair hD (z.1,(z.2:ZMod M)))*
        pairedFrequencyResidueIndicator K h k (projectedRingPair hR (z.1,(z.2:ZMod M)))*
        primeResidueIndicatorB h k hs ks (projectedRingPair hB (z.1,(z.2:ZMod M)))) := by
    funext z
    have ha : mixedExtension w (projectedRingPair hA (z.1,(z.2:ZMod M)))=w (mixedPairMap hA z) := by
      rw [←mixedExtension_coe w (mixedPairMap hA z)]
      rfl
    rw [ha,liftedResidueTest_eq_paired_four_blocks K h k hs ks hroot hsmall hlarge klarge
      hu ku hle hsame had hV g hprime hg M hd hA hD hR hB]
    simp only [ringPairReduction,projectedRingPair,mul_assoc]
  rw [he]
  simpa only [mixedExtension_coe] using four_mixed_projected_product_average (rootModulus h) outside.prod
    (frequencyModulus h k (K+2)) (representativeModulus h k)
    (had.2.2.2 (K+2)) hCRT hA hD hR hB
    (fun z=>mixedExtension w z*rootResidueIndicator h z)
    (residuePairSpectator g outside outside.prod h k)
    (pairedFrequencyResidueIndicator K h k) (primeResidueIndicatorB h k hs ks)

end Ostmann.Arithmetic.HistorySignedResidueWeightedAverages

end

end OAI
