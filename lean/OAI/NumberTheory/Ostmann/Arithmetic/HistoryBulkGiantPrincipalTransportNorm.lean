import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportNormBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryPairPattern HistoryCRTIntegration HistorySignedSpectatorCRT
open HistoryBulkReferenceTests HistoryBulkResidueNormSum HistoryFrequencyResidues
open HistoryPrincipalIntegralAverage ResidueHaar HistorySignedResidueFactorization
open HistoryGiantWeightedPriorReplacement

variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem norm_primeResidueIndicatorAt_le (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (z : ZMod (representativeModulus h k)×ZMod (representativeModulus h k)) :
    ‖primeResidueIndicatorAt h k hs ks v z‖≤1 := by
  classical
  unfold primeResidueIndicatorAt guardIndicator
  split_ifs <;> simp

section Bounds
variable (d : Decomposition) (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (newh newk : History l)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ) (M : ℕ)
    (hA : rootModulus newh∣M) (hD : outside.prod∣M)
    (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ)
    (hout : ∀q∈outside,q.Prime) (BW : ℝ) (hBW : 0≤BW) (hW : ∀z,‖fA z‖≤BW)

include hout hBW hW

theorem norm_referenceResidueTest_le (z : ZMod M×ZMod M) :
    ‖referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA z‖≤
      BW*(outside.prod:ℝ)^(2^(l+1)) := by
  unfold referenceResidueTest
  simp only [norm_mul]
  calc
    _ ≤ BW*(outside.prod:ℝ)^(2^(l+1))*1*1 := by
      gcongr
      · exact hW _
      · exact norm_actual_residuePairSpectator_le d outside hout outside.prod newh newk _
      · exact independentRTest_norm_le K h k σ _ x
      · exact norm_primeResidueIndicatorAt_le h k hs ks v _
    _ = _ := by ring

variable [NeZero M]

theorem sum_norm_reference_primeTest_le :
    (∑u : Bool→(ZMod M)ˣ,
      ‖primeTest (referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA) u‖)≤
      BW*(M.totient:ℝ)^2*(outside.prod:ℝ)^(2^(l+1)) := by
  calc
    _ ≤ ∑_u : Bool→(ZMod M)ˣ,BW*(outside.prod:ℝ)^(2^(l+1)) :=
      Finset.sum_le_sum (fun u _=>norm_referenceResidueTest_le
        d K h k hs ks newh newk σ x v M hA hD hR hB fA hout BW hBW hW _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_bool,ZMod.card_units_eq_totient,Nat.cast_pow]
      ring

theorem sum_norm_reference_mixedTest_le :
    (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,
      ‖mixedTest (referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA) r u‖)≤
      BW*(M:ℝ)*(M.totient:ℝ)*(outside.prod:ℝ)^(2^(l+1)) := by
  calc
    _ ≤ ∑_r : ZMod M,∑_u : Unit→(ZMod M)ˣ,BW*(outside.prod:ℝ)^(2^(l+1)) := by
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun u _=>norm_referenceResidueTest_le
        d K h k hs ks newh newk σ x v M hA hD hR hB fA hout BW hBW hW _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_unit,pow_one,ZMod.card_units_eq_totient,ZMod.card]
      ring

theorem sum_norm_reference_primeTest_le_modulus :
    (∑u : Bool→(ZMod M)ˣ,
      ‖primeTest (referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA) u‖)≤
      BW*(M:ℝ)^(2+2^(l+1)) := by
  have ho : (outside.prod:ℝ)≤M := by exact_mod_cast Nat.le_of_dvd (NeZero.pos M) hD
  have ht : (M.totient:ℝ)≤M := by exact_mod_cast Nat.totient_le M
  refine (sum_norm_reference_primeTest_le d K h k hs ks newh newk σ x v M hA hD hR hB fA hout BW hBW hW).trans ?_
  calc
    _ ≤ BW*(M:ℝ)^2*(M:ℝ)^(2^(l+1)) := by gcongr
    _ = _ := by rw [pow_add (M:ℝ) 2 (2^(l+1))]; ring

theorem sum_norm_reference_mixedTest_le_modulus :
    (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,
      ‖mixedTest (referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA) r u‖)≤
      BW*(M:ℝ)^(2+2^(l+1)) := by
  have ho : (outside.prod:ℝ)≤M := by exact_mod_cast Nat.le_of_dvd (NeZero.pos M) hD
  have ht : (M.totient:ℝ)≤M := by exact_mod_cast Nat.totient_le M
  refine (sum_norm_reference_mixedTest_le d K h k hs ks newh newk σ x v M hA hD hR hB fA hout BW hBW hW).trans ?_
  calc
    _ ≤ BW*(M:ℝ)*(M:ℝ)*(M:ℝ)^(2^(l+1)) := by gcongr
    _ = _ := by rw [pow_add (M:ℝ) 2 (2^(l+1)),pow_two]; ring

theorem sum_norm_reference_primeTest_le_modulus_succ (hWM : BW≤M) :
    (∑u : Bool→(ZMod M)ˣ,
      ‖primeTest (referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA) u‖)≤
      (M:ℝ)^(3+2^(l+1)) := by
  refine (sum_norm_reference_primeTest_le_modulus d K h k hs ks newh newk σ x v M hA hD hR hB fA hout BW hBW hW).trans ?_
  calc
    _ ≤ (M:ℝ)*(M:ℝ)^(2+2^(l+1)) := mul_le_mul_of_nonneg_right hWM (by positivity)
    _ = _ := by rw [show 3+2^(l+1)=(2+2^(l+1))+1 by omega,pow_succ]; ring

theorem sum_norm_reference_mixedTest_le_modulus_succ (hWM : BW≤M) :
    (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,
      ‖mixedTest (referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA) r u‖)≤
      (M:ℝ)^(3+2^(l+1)) := by
  refine (sum_norm_reference_mixedTest_le_modulus d K h k hs ks newh newk σ x v M hA hD hR hB fA hout BW hBW hW).trans ?_
  calc
    _ ≤ (M:ℝ)*(M:ℝ)^(2+2^(l+1)) := mul_le_mul_of_nonneg_right hWM (by positivity)
    _ = _ := by rw [show 3+2^(l+1)=(2+2^(l+1))+1 by omega,pow_succ]; ring

end Bounds
end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
