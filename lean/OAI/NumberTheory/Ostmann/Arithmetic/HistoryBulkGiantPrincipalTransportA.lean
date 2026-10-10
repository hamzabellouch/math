import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueWeightedAverages

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryPairPattern HistoryCRTIntegration HistorySignedSpectatorCRT
open HistoryBulkReferenceTests HistoryBulkResidueNormSum HistoryFrequencyResidues
open HistoryPrincipalIntegralAverage ResidueHaar HistorySignedResidueFactorization
open HistorySignedResidueWeightedAverages HistoryDiagonalSmallAverage DiagonalSmallResidueNorm
variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

section Average
variable (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (newh newk : History l) (g : (q:ℕ)→ZMod q→ℂ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ) (M : ℕ)
    (hA : rootModulus newh∣M) (hD : outside.prod∣M)
    (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
    [NeZero (rootModulus newh)] [NeZero outside.prod]
    [NeZero (frequencyModulus h k (K+2))] [NeZero (representativeModulus h k)] [NeZero M]
    (hc : (rootModulus newh).Coprime outside.prod ∧
      (rootModulus newh).Coprime (frequencyModulus h k (K+2)) ∧
      (rootModulus newh).Coprime (representativeModulus h k) ∧
      outside.prod.Coprime (frequencyModulus h k (K+2)) ∧
      outside.prod.Coprime (representativeModulus h k) ∧
      (frequencyModulus h k (K+2)).Coprime (representativeModulus h k))
    (hd : rootModulus newh*outside.prod*frequencyModulus h k (K+2)*representativeModulus h k∣M)
include hc hd

theorem reference_mixed_small_average
    (d : Decomposition) (outerU xs : List SmallSlot)
    (hslots : newh.root.small.Perm (outerU++xs)) (D₀ P₀ q₀ : ℕ) (v₀ : ℤ)
    [∀i,Fact (smallPrime xs outerU i).Prime] (huA : SmallUnitData D₀ P₀ q₀ outerU xs v₀) :
    average (fun z : MixedPair M =>
      referenceResidueTest K h k hs ks newh newk g σ x v M hA hD hR hB
        (fun a => rootResidueIndicator newh a * mixedExtension
          (fun u => (rootSmallTest d newh outerU xs hslots D₀ P₀ q₀ v₀ huA u:ℂ)) a)
        (z.1,z.2)) =
    ((∏i : Fin outerU.length, (((outerU[i].value-1:ℕ):ℝ)/outerU[i].value):ℝ):ℂ)*
      average (fun z : MixedPair outside.prod=>residuePairSpectator g outside outside.prod newh newk (z.1,z.2))*
      average (fun z : MixedPair (frequencyModulus h k (K+2))=>independentRTest K h k σ
        ((z.1:ZMod (frequencyModulus h k (K+2))),(z.2:ZMod (frequencyModulus h k (K+2)))) x)*
      average (fun z : MixedPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)) := by
  rw [reference_mixed_average K h k hs ks newh newk g σ x v M hA hD hR hB _ hc hd]
  simp only [mixedExtension_coe]
  rw [rootSmallTest_mixed_average]

end Average
end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
