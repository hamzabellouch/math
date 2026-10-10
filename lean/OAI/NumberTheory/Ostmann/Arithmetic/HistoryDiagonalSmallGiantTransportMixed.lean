import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjection
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportResidues

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration
open HistoryCRTProjection ResidueHaar

theorem extendedRootSmallTest_mixed (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (z : MixedPair (rootModulus h)) :
    extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ (z.1,(z.2:ZMod (rootModulus h)))=
      rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z := by
  unfold extendedRootSmallTest
  rw [dite_eq_left z.2.isUnit]
  congr 1
  apply Prod.ext
  · rfl
  · apply Units.ext
    exact IsUnit.unit_spec _

theorem liftedRootSmallTest_mixed_eq (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (M : ℕ)
    (hA : rootModulus h ∣ M) (z : MixedPair M) :
    liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA (z.1,(z.2:ZMod M))=
      rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ (mixedPairMap hA z) := by
  change extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀
    ((mixedPairMap hA z).1,((mixedPairMap hA z).2:ZMod (rootModulus h))) = _
  exact extendedRootSmallTest_mixed d h outerU xs hslots D P₀ q₀ v hu₀ _

theorem liftedRootSmallTest_norm_le_modulus (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (M : ℕ) (hM : 0 < M)
    (hA : rootModulus h ∣ M) (z : ZMod M × ZMod M) :
    ‖(liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA z:ℂ)‖ ≤ (M:ℝ) := by
  apply (liftedRootSmallTest_norm_le d h outerU xs hslots D P₀ q₀ v hu₀ M hA z).trans
  exact_mod_cast Nat.le_of_dvd hM hA

theorem liftedRootSmallTest_mixed_average (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (M : ℕ) [NeZero M]
    (hA : rootModulus h ∣ M) :
    average (fun z : MixedPair M=>
      (liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA (z.1,(z.2:ZMod M)):ℂ))=
      ((∏i : Fin outerU.length,(((outerU[i].value-1:ℕ):ℝ)/outerU[i].value):ℝ):ℂ) := by
  have : NeZero (rootModulus h) := ⟨by
    intro hz
    have hh := hA
    rw [hz,zero_dvd_iff] at hh
    exact (NeZero.ne M) hh⟩
  simp_rw [liftedRootSmallTest_mixed_eq]
  rw [mixed_pair_average hA (fun z : MixedPair (rootModulus h)=>
    (rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z:ℂ))]
  simpa only [rootResidueIndicator_mul_rootSmallTest] using
    rootSmallTest_mixed_average d h outerU xs hslots D P₀ q₀ v hu₀

theorem norm_liftedRootSmallTest_mixed_average_le_one (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (M : ℕ) [NeZero M]
    (hA : rootModulus h ∣ M) :
    ‖average (fun z : MixedPair M=>
      (liftedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ M hA (z.1,(z.2:ZMod M)):ℂ))‖ ≤ 1 := by
  have : NeZero (rootModulus h) := ⟨by
    intro hz
    have hh := hA
    rw [hz,zero_dvd_iff] at hh
    exact (NeZero.ne M) hh⟩
  simp_rw [liftedRootSmallTest_mixed_eq]
  rw [mixed_pair_average hA (fun z : MixedPair (rootModulus h)=>
    (rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z:ℂ))]
  simpa only [rootResidueIndicator_mul_rootSmallTest] using
    norm_rootSmallTest_mixed_average_le_one d h outerU xs hslots D P₀ q₀ v hu₀

end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI
