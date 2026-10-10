import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityBAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueAverages
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySignedResidueMainFactors
open Construction HistorySignedResidues HistoryCRTIntegration HistorySignedResidueFactorization
open HistorySupportReduction HistoryPairPattern HistoryPairRows HistoryFrequencyResidues
open HistoryRepresentativeSourceSeparation HistorySignedSpectatorCRT ResidueHaar
open HistorySignedSpectatorDiagramAverage HistorySignedSpectatorDiagram
open HistoryPairSquareProbability HistoryPairRepresentatives

theorem root_unit_average {l : ℕ} (h : History l) [NeZero (rootModulus h)] :
    average (fun z : UnitPair (rootModulus h)=>rootResidueIndicator h (z.1,z.2))=1 := by
  have he : (fun z : UnitPair (rootModulus h)=>rootResidueIndicator h (z.1,z.2))=
      (fun _ : UnitPair (rootModulus h)=>(1:ℂ)) := by
    funext z
    simp only [rootResidueIndicator,guardIndicator,z.1.isUnit,z.2.isUnit,and_self,ite_true]
  rw [he]
  have hc : (Fintype.card (UnitPair (rootModulus h)):ℂ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [average,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ hc

variable (d : Decomposition) (K : ℕ) {l : ℕ} (h k : History (l+1))
variable {V : ℕ→ℕ} {outside : List ℕ}
variable (hs : h.Supported V outside) (ks : k.Supported V outside)
variable (hroot : RootGiantsAgree h k) (hsmall : h.root.small.Perm k.root.small)
variable (hlarge : LargePrimes V h) (klarge : LargePrimes V k)
variable (hu : FrequencyUnits (pairedFrequencyProduct h k) h)
variable (ku : FrequencyUnits (pairedFrequencyProduct h k) k) (hle : l+1≤K)
variable (had : PairAdmissible h k outside)
variable (hV : ∀i : Occurrences h k,∀j≤l+1,V j<(slot h k i).value)
variable (hprime : ∀q∈outside,q.Prime) (hVo : ∀q∈outside,∀j≤l+1,V j<q)
variable [NeZero (pairModulus h k outside)] (M : ℕ) [NeZero M]
variable [NeZero (rootModulus h)] [NeZero outside.prod]
variable [NeZero (frequencyModulus h k (K+2))] [NeZero (representativeModulus h k)]
variable (hd : pairModulus h k outside∣M)
variable (hA : rootModulus h∣M) (hD : outside.prod∣M)
variable (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
variable (hCRT : crtModulus h k outside (K+2)∣M)
include hroot hsmall hlarge klarge hu ku hle had hV hprime hVo hA hD hR hB hCRT

theorem unit_average_eq_main_factors :
    letI := primeAtNeZero hprime
    average (fun z : UnitPair M=>liftedResidueTest (residueTransform d) V outside h k M hd ((z.1:ZMod M),(z.2:ZMod M)))=
      (∏i:Fin outside.length,average (localDiagramPair h k hs ks (primeAt outside i)
        (List.get_mem outside i) (hprime _ (List.get_mem outside i))
        (hVo _ (List.get_mem outside i)) (residueTransform d)))*
      average (fun z : UnitPair (frequencyModulus h k (K+2))=>independentFrequencyResidueIndicator K h k (z.1,z.2))*
      ((∏r : Representative h k,actualUnitSquareProbability h k hs ks r):ℂ) := by
  let := primeAtNeZero hprime
  have he := HistorySignedResidueAverages.unit_average_eq_four_blocks K h k hs ks
    hroot hsmall hlarge klarge hu ku hle had hV (residueTransform d) hprime
    (fun q _=>actual_residueTransform_zero d q) M hd hA hD hR hB hCRT
  rw [he,actual_unit_average_eq_diagram_averages d h k hs ks had hprime hVo,
    unit_B_average_eq_product h k hs ks had]
  rw [root_unit_average,one_mul]

theorem mixed_average_eq_main_factors :
    letI := primeAtNeZero hprime
    average (fun z : MixedPair M=>liftedResidueTest (residueTransform d) V outside h k M hd (z.1,(z.2:ZMod M)))=
      average (fun z : MixedPair (rootModulus h)=>rootResidueIndicator h (z.1,z.2))*
      (∏i:Fin outside.length,average (localMixedDiagramPair h k hs ks (primeAt outside i)
        (List.get_mem outside i) (hprime _ (List.get_mem outside i))
        (hVo _ (List.get_mem outside i)) (residueTransform d)))*
      average (fun z : MixedPair (frequencyModulus h k (K+2))=>independentFrequencyResidueIndicator K h k (z.1,z.2))*
      ((∏r : Representative h k,actualMixedSquareProbability h k hs ks r):ℂ) := by
  let := primeAtNeZero hprime
  have he := HistorySignedResidueAverages.mixed_average_eq_four_blocks K h k hs ks
    hroot hsmall hlarge klarge hu ku hle had hV (residueTransform d) hprime
    (fun q _=>actual_residueTransform_zero d q) M hd hA hD hR hB hCRT
  rw [he,actual_mixed_average_eq_diagram_averages d h k hs ks had hprime hVo,
    mixed_B_average_eq_product h k hs ks had]

end Ostmann.Arithmetic.HistorySignedResidueMainFactors

end

end OAI
