import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportModulus
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

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
open HistoryBulkReferenceNewModuli
variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
section Average
variable (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (newh newk : History l) (d : Decomposition)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ)
    [NeZero (rootModulus newh)] [NeZero outside.prod]
    [NeZero (frequencyModulus h k (K+2))] [NeZero (representativeModulus h k)] [NeZero (newComparisonModulus newh h k outside K)]
    (hc : NewCRTCompatible newh h k outside K)
include hc

theorem new_reference_unit_root_average :
    average (fun z : UnitPair (newComparisonModulus newh h k outside K) =>
      newReferenceResidueTest d K h k hs ks newh newk σ x v (rootResidueIndicator newh) (z.1,z.2)) =
      average (fun z : UnitPair outside.prod=>residuePairSpectator (residueTransform d) outside outside.prod newh newk (z.1,z.2))*
      average (fun z : UnitPair (frequencyModulus h k (K+2))=>independentRTest K h k σ
        ((z.1:ZMod (frequencyModulus h k (K+2))),(z.2:ZMod (frequencyModulus h k (K+2)))) x)*
      average (fun z : UnitPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)) :=
  reference_unit_root_average K h k hs ks newh newk (residueTransform d) σ x v
    (newComparisonModulus newh h k outside K) (new_A_dvd newh h k outside K)
    (new_D_dvd newh h k outside K) (new_R_dvd newh h k outside K)
    (new_B_dvd newh h k outside K) hc dvd_rfl

theorem new_reference_mixed_small_average
    (outerU xs : List SmallSlot) (hslots : newh.root.small.Perm (outerU++xs))
    (D₀ P₀ q₀ : ℕ) (v₀ : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (huA : SmallUnitData D₀ P₀ q₀ outerU xs v₀) :
    average (fun z : MixedPair (newComparisonModulus newh h k outside K) =>
      newReferenceResidueTest d K h k hs ks newh newk σ x v
        (fun a => rootResidueIndicator newh a * mixedExtension
          (fun u => (rootSmallTest d newh outerU xs hslots D₀ P₀ q₀ v₀ huA u:ℂ)) a) (z.1,z.2)) =
      ((∏i : Fin outerU.length, (((outerU[i].value-1:ℕ):ℝ)/outerU[i].value):ℝ):ℂ)*
      average (fun z : MixedPair outside.prod=>residuePairSpectator (residueTransform d) outside outside.prod newh newk (z.1,z.2))*
      average (fun z : MixedPair (frequencyModulus h k (K+2))=>independentRTest K h k σ
        ((z.1:ZMod (frequencyModulus h k (K+2))),(z.2:ZMod (frequencyModulus h k (K+2)))) x)*
      average (fun z : MixedPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)) :=
  reference_mixed_small_average K h k hs ks newh newk (residueTransform d) σ x v
    (newComparisonModulus newh h k outside K) (new_A_dvd newh h k outside K)
    (new_D_dvd newh h k outside K) (new_R_dvd newh h k outside K)
    (new_B_dvd newh h k outside K) hc dvd_rfl d outerU xs hslots D₀ P₀ q₀ v₀ huA

end Average
end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
