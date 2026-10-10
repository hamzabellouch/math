import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportA
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportNorm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportBounds

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
open HistoryGiantWeightedPriorReplacement
variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

lemma norm_rootResidueIndicator_le_one (h : History l) (z : ZMod (rootModulus h)×ZMod (rootModulus h)) :
    ‖rootResidueIndicator h z‖ ≤ 1 := by
  classical
  unfold rootResidueIndicator guardIndicator
  split_ifs <;> simp

lemma norm_mixed_rootSmallTest_le (d : Decomposition) (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v) (z : ZMod (rootModulus h)×ZMod (rootModulus h)) :
    ‖rootResidueIndicator h z * mixedExtension
      (fun u => (rootSmallTest d h outerU xs hslots D P q v hu u:ℂ)) z‖ ≤ (rootModulus h:ℝ) := by
  classical
  rw [norm_mul]
  have he : ‖mixedExtension (fun u => (rootSmallTest d h outerU xs hslots D P q v hu u:ℂ)) z‖ ≤
      (rootModulus h:ℝ) := by
    unfold mixedExtension
    split_ifs
    · exact rootSmallTest_norm_le d h outerU xs hslots D P q v hu _
    · simp
  exact (mul_le_mul (norm_rootResidueIndicator_le_one h z) he (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem reference_test_budget (d : Decomposition) (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (newh newk : History l) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ) (M : ℕ) [NeZero M]
    (hA : rootModulus newh∣M) (hD : outside.prod∣M)
    (hR : frequencyModulus h k (K+2)∣M) (hB : representativeModulus h k∣M)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ)
    (hout : ∀q∈outside,q.Prime) (hW : ∀z,‖fA z‖≤(M:ℝ)) :
    let R := referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v M hA hD hR hB fA
    (∀z,‖R z‖≤(M:ℝ)^(3+2^(l+1))) ∧
    (∑u : Bool→(ZMod M)ˣ,‖primeTest R u‖)≤(M:ℝ)^(3+2^(l+1)) ∧
    (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,‖mixedTest R r u‖)≤(M:ℝ)^(3+2^(l+1)) := by
  dsimp only
  refine ⟨?_,sum_norm_reference_primeTest_le_modulus_succ d K h k hs ks newh newk σ x v M
    hA hD hR hB fA hout M (Nat.cast_nonneg M) hW le_rfl,
    sum_norm_reference_mixedTest_le_modulus_succ d K h k hs ks newh newk σ x v M
    hA hD hR hB fA hout M (Nat.cast_nonneg M) hW le_rfl⟩
  intro z
  have ho : (outside.prod:ℝ)≤M := by exact_mod_cast Nat.le_of_dvd (NeZero.pos M) hD
  have hm : (1:ℝ)≤M := by exact_mod_cast NeZero.pos M
  refine (norm_referenceResidueTest_le d K h k hs ks newh newk σ x v M hA hD hR hB fA
    hout M (Nat.cast_nonneg M) hW z).trans ?_
  calc
    _ ≤ (M:ℝ)*(M:ℝ)^(2^(l+1)) := by gcongr
    _ = (M:ℝ)^(1+2^(l+1)) := by rw [pow_add (M:ℝ) 1 (2^(l+1)),pow_one]
    _ ≤ _ := pow_le_pow_right₀ hm (by omega)

lemma root_test_norm_le_modulus (newh : History l) (M : ℕ) [NeZero M]
    (z : ZMod (rootModulus newh)×ZMod (rootModulus newh)) :
    ‖rootResidueIndicator newh z‖≤(M:ℝ) :=
  (norm_rootResidueIndicator_le_one newh z).trans (by exact_mod_cast NeZero.pos M)

lemma mixed_small_test_norm_le_modulus (d : Decomposition) (newh : History l)
    (outerU xs : List SmallSlot) (hslots : newh.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu : SmallUnitData D P q outerU xs v) (M : ℕ) [NeZero M]
    (hA : rootModulus newh∣M) (z : ZMod (rootModulus newh)×ZMod (rootModulus newh)) :
    ‖rootResidueIndicator newh z * mixedExtension
      (fun u => (rootSmallTest d newh outerU xs hslots D P q v hu u:ℂ)) z‖≤(M:ℝ) :=
  (norm_mixed_rootSmallTest_le d newh outerU xs hslots D P q v hu z).trans
    (by exact_mod_cast Nat.le_of_dvd (NeZero.pos M) hA)

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
