import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportFlags
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTFourProducts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueMainFactors
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryPairPattern HistoryCRTIntegration HistorySignedSpectatorCRT
open HistoryBulkReferenceTests HistoryBulkResidueNormSum HistoryFrequencyResidues
open HistoryPrincipalIntegralAverage ResidueHaar HistorySignedResidueFactorization

variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

def referenceResidueTest (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (newh newk : History l) (g : (q:ℕ)→ZMod q→ℂ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ) (M : ℕ)
    (hA : rootModulus newh∣M) (hD : outside.prod∣M)
    (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ)
    (z : ZMod M×ZMod M) : ℂ :=
  fA (projectedRingPair hA z)*
    residuePairSpectator g outside outside.prod newh newk (projectedRingPair hD z)*
    independentRTest K h k σ (projectedRingPair hR z) x*
    primeResidueIndicatorAt h k hs ks v (projectedRingPair hB z)

section Average
variable (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (newh newk : History l) (g : (q:ℕ)→ZMod q→ℂ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ) (M : ℕ)
    (hA : rootModulus newh∣M) (hD : outside.prod∣M)
    (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ)
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

theorem reference_unit_average :
    average (fun z : UnitPair M =>
      referenceResidueTest K h k hs ks newh newk g σ x v M hA hD hR hB fA (z.1,z.2)) =
    average (fun z : UnitPair (rootModulus newh)=>fA (z.1,z.2))*
      average (fun z : UnitPair outside.prod=>residuePairSpectator g outside outside.prod newh newk (z.1,z.2))*
      average (fun z : UnitPair (frequencyModulus h k (K+2))=>independentRTest K h k σ ((z.1:ZMod (frequencyModulus h k (K+2))),
        (z.2:ZMod (frequencyModulus h k (K+2)))) x)*
      average (fun z : UnitPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)) := by
  unfold referenceResidueTest
  exact four_unit_projected_product_average _ _ _ _ hc hd hA hD hR hB fA
    (residuePairSpectator g outside outside.prod newh newk)
    (fun z => independentRTest K h k σ z x) (primeResidueIndicatorAt h k hs ks v)

theorem reference_mixed_average :
    average (fun z : MixedPair M =>
      referenceResidueTest K h k hs ks newh newk g σ x v M hA hD hR hB fA (z.1,z.2)) =
    average (fun z : MixedPair (rootModulus newh)=>fA (z.1,z.2))*
      average (fun z : MixedPair outside.prod=>residuePairSpectator g outside outside.prod newh newk (z.1,z.2))*
      average (fun z : MixedPair (frequencyModulus h k (K+2))=>independentRTest K h k σ ((z.1:ZMod (frequencyModulus h k (K+2))),
        (z.2:ZMod (frequencyModulus h k (K+2)))) x)*
      average (fun z : MixedPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)) := by
  unfold referenceResidueTest
  exact four_mixed_projected_product_average _ _ _ _ hc hd hA hD hR hB fA
    (residuePairSpectator g outside outside.prod newh newk)
    (fun z => independentRTest K h k σ z x) (primeResidueIndicatorAt h k hs ks v)

omit fA in

theorem reference_unit_root_average :
    average (fun z : UnitPair M =>
      referenceResidueTest K h k hs ks newh newk g σ x v M hA hD hR hB
        (rootResidueIndicator newh) (z.1,z.2)) =
      average (fun z : UnitPair outside.prod=>residuePairSpectator g outside outside.prod newh newk (z.1,z.2))*
      average (fun z : UnitPair (frequencyModulus h k (K+2))=>independentRTest K h k σ ((z.1:ZMod (frequencyModulus h k (K+2))),
        (z.2:ZMod (frequencyModulus h k (K+2)))) x)*
      average (fun z : UnitPair (representativeModulus h k)=>primeResidueIndicatorAt h k hs ks v (z.1,z.2)) := by
  rw [reference_unit_average K h k hs ks newh newk g σ x v M hA hD hR hB
    (rootResidueIndicator newh) hc hd,HistorySignedResidueMainFactors.root_unit_average,one_mul]

end Average
end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
