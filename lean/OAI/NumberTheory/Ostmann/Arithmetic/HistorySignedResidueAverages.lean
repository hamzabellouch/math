import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTFourProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationPairedCRT

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueAverages
open Construction HistorySignedResidues HistoryCRTIntegration HistorySignedResidueFactorization
open HistorySupportReduction HistoryPairPattern HistoryPairRows HistoryFrequencyResidues
open HistoryRepresentativeSourceSeparation HistorySignedSpectatorCRT ResidueHaar

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

theorem unit_average_eq_four_blocks :
    average (fun z : UnitPair M => liftedResidueTest g V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M))) =
      average (fun z : UnitPair (rootModulus h) => rootResidueIndicator h (z.1,z.2))*
      average (fun z : UnitPair outside.prod => residuePairSpectator g outside outside.prod h k (z.1,z.2))*
      average (fun z : UnitPair (frequencyModulus h k (K+2)) => independentFrequencyResidueIndicator K h k (z.1,z.2))*
      average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2)) := by
  have he : (fun z : UnitPair M => liftedResidueTest g V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M))) =
      (fun z : UnitPair M => rootResidueIndicator h (projectedRingPair hA ((z.1:ZMod M),(z.2:ZMod M))) *
        residuePairSpectator g outside outside.prod h k (projectedRingPair hD ((z.1:ZMod M),(z.2:ZMod M))) *
        independentFrequencyResidueIndicator K h k (projectedRingPair hR ((z.1:ZMod M),(z.2:ZMod M))) *
        primeResidueIndicatorB h k hs ks (projectedRingPair hB ((z.1:ZMod M),(z.2:ZMod M)))) := by
    funext z
    exact liftedResidueTest_eq_four_blocks K h k hs ks hroot hsmall hlarge klarge hu ku hle had hV g hprime hg M hd hA hD hR hB ((z.1:ZMod M),(z.2:ZMod M))
  rw [he]
  exact four_unit_projected_product_average (rootModulus h) outside.prod
    (frequencyModulus h k (K+2)) (representativeModulus h k)
    (had.2.2.2 (K+2)) hCRT hA hD hR hB
    (rootResidueIndicator h) (residuePairSpectator g outside outside.prod h k)
    (independentFrequencyResidueIndicator K h k) (primeResidueIndicatorB h k hs ks)

theorem mixed_average_eq_four_blocks :
    average (fun z : MixedPair M => liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M))) =
      average (fun z : MixedPair (rootModulus h) => rootResidueIndicator h (z.1,z.2))*
      average (fun z : MixedPair outside.prod => residuePairSpectator g outside outside.prod h k (z.1,z.2))*
      average (fun z : MixedPair (frequencyModulus h k (K+2)) => independentFrequencyResidueIndicator K h k (z.1,z.2))*
      average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2)) := by
  have he : (fun z : MixedPair M => liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M))) =
      (fun z : MixedPair M => rootResidueIndicator h (projectedRingPair hA (z.1,(z.2:ZMod M))) *
        residuePairSpectator g outside outside.prod h k (projectedRingPair hD (z.1,(z.2:ZMod M))) *
        independentFrequencyResidueIndicator K h k (projectedRingPair hR (z.1,(z.2:ZMod M))) *
        primeResidueIndicatorB h k hs ks (projectedRingPair hB (z.1,(z.2:ZMod M)))) := by
    funext z
    exact liftedResidueTest_eq_four_blocks K h k hs ks hroot hsmall hlarge klarge hu ku hle had hV g hprime hg M hd hA hD hR hB (z.1,(z.2:ZMod M))
  rw [he]
  exact four_mixed_projected_product_average (rootModulus h) outside.prod
    (frequencyModulus h k (K+2)) (representativeModulus h k)
    (had.2.2.2 (K+2)) hCRT hA hD hR hB
    (rootResidueIndicator h) (residuePairSpectator g outside outside.prod h k)
    (independentFrequencyResidueIndicator K h k) (primeResidueIndicatorB h k hs ks)

theorem paired_unit_average_eq_four_blocks
    (hsame : frequencyLeaves ((pairedFrequencyProduct h k)^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h k)^(K+2)) k) :
    average (fun z : UnitPair M => liftedResidueTest g V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M))) =
      average (fun z : UnitPair (rootModulus h) => rootResidueIndicator h (z.1,z.2))*
      average (fun z : UnitPair outside.prod => residuePairSpectator g outside outside.prod h k (z.1,z.2))*
      average (fun z : UnitPair (frequencyModulus h k (K+2)) => pairedFrequencyResidueIndicator K h k (z.1,z.2))*
      average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2)) := by
  have he : (fun z : UnitPair M => liftedResidueTest g V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M))) =
      (fun z : UnitPair M => rootResidueIndicator h (projectedRingPair hA ((z.1:ZMod M),(z.2:ZMod M))) *
        residuePairSpectator g outside outside.prod h k (projectedRingPair hD ((z.1:ZMod M),(z.2:ZMod M))) *
        pairedFrequencyResidueIndicator K h k (projectedRingPair hR ((z.1:ZMod M),(z.2:ZMod M))) *
        primeResidueIndicatorB h k hs ks (projectedRingPair hB ((z.1:ZMod M),(z.2:ZMod M)))) := by
    funext z
    exact liftedResidueTest_eq_paired_four_blocks K h k hs ks hroot hsmall hlarge klarge hu ku hle hsame had hV g hprime hg M hd hA hD hR hB ((z.1:ZMod M),(z.2:ZMod M))
  rw [he]
  exact four_unit_projected_product_average (rootModulus h) outside.prod
    (frequencyModulus h k (K+2)) (representativeModulus h k)
    (had.2.2.2 (K+2)) hCRT hA hD hR hB
    (rootResidueIndicator h) (residuePairSpectator g outside outside.prod h k)
    (pairedFrequencyResidueIndicator K h k) (primeResidueIndicatorB h k hs ks)

theorem paired_mixed_average_eq_four_blocks
    (hsame : frequencyLeaves ((pairedFrequencyProduct h k)^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h k)^(K+2)) k) :
    average (fun z : MixedPair M => liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M))) =
      average (fun z : MixedPair (rootModulus h) => rootResidueIndicator h (z.1,z.2))*
      average (fun z : MixedPair outside.prod => residuePairSpectator g outside outside.prod h k (z.1,z.2))*
      average (fun z : MixedPair (frequencyModulus h k (K+2)) => pairedFrequencyResidueIndicator K h k (z.1,z.2))*
      average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorB h k hs ks (z.1,z.2)) := by
  have he : (fun z : MixedPair M => liftedResidueTest g V outside h k M hd (z.1,(z.2:ZMod M))) =
      (fun z : MixedPair M => rootResidueIndicator h (projectedRingPair hA (z.1,(z.2:ZMod M))) *
        residuePairSpectator g outside outside.prod h k (projectedRingPair hD (z.1,(z.2:ZMod M))) *
        pairedFrequencyResidueIndicator K h k (projectedRingPair hR (z.1,(z.2:ZMod M))) *
        primeResidueIndicatorB h k hs ks (projectedRingPair hB (z.1,(z.2:ZMod M)))) := by
    funext z
    exact liftedResidueTest_eq_paired_four_blocks K h k hs ks hroot hsmall hlarge klarge hu ku hle hsame had hV g hprime hg M hd hA hD hR hB (z.1,(z.2:ZMod M))
  rw [he]
  exact four_mixed_projected_product_average (rootModulus h) outside.prod
    (frequencyModulus h k (K+2)) (representativeModulus h k)
    (had.2.2.2 (K+2)) hCRT hA hD hR hB
    (rootResidueIndicator h) (residuePairSpectator g outside outside.prod h k)
    (pairedFrequencyResidueIndicator K h k) (primeResidueIndicatorB h k hs ks)

end Ostmann.Arithmetic.HistorySignedResidueAverages

end

end OAI
