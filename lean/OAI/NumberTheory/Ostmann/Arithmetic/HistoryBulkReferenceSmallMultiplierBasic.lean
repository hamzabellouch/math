import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportExtension
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueWeightedAverages

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier
open Construction DiagonalSmallResidueNorm HistoryDiagonalSmallAverage
open HistorySignedResidueFactorization HistorySignedResidueWeightedAverages
open HistoryCRTIntegration

theorem mixedExtension_rootSmallTest (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (v : ℤ) [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (z : ZMod (rootModulus h) × ZMod (rootModulus h)) :
    mixedExtension (fun a => (rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ a : ℂ)) z =
      (extendedRootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z : ℂ) := by
  classical
  by_cases hq : IsUnit z.2
  · simp only [mixedExtension, extendedRootSmallTest, dite_eq_left hq]
  · simp only [mixedExtension, extendedRootSmallTest, dite_eq_right hq, Complex.ofReal_zero]

theorem diagonalSmallMultiplier_mul_rootResidueIndicator (d : Decomposition)
    {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ P q : ℕ) (v : ℤ) [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) :
    (diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs : ℂ) *
        rootResidueIndicator h ((P : ZMod (rootModulus h)), (q : ZMod (rootModulus h))) =
      rootResidueIndicator h ((P : ZMod (rootModulus h)), (q : ZMod (rootModulus h))) *
        mixedExtension (fun z => (rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z : ℂ))
          ((P : ZMod (rootModulus h)), (q : ZMod (rootModulus h))) := by
  classical
  rw [mixedExtension_rootSmallTest]
  by_cases hu : IsUnit (P : ZMod (rootModulus h)) ∧ IsUnit (q : ZMod (rootModulus h))
  · rw [extendedRootSmallTest_natCast d h outerU xs hslots D P₀ q₀ P q v hu₀ hu.1 hu.2]
    exact mul_comm _ _
  · simp only [rootResidueIndicator, guardIndicator, ite_eq_right hu, mul_zero, zero_mul]

theorem diagonalSmallMultiplier_mul_rootResidueIndicator_intCast (d : Decomposition)
    {l : ℕ} (h : History l) (outerU xs : List SmallSlot)
    (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ : ℕ) (P Q : ℤ) (v : ℤ) [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (diagonalSmallMultiplier d (D*halfProduct P.toNat outerU) v Q.toNat xs : ℂ) *
        rootResidueIndicator h ((P : ZMod (rootModulus h)), (Q : ZMod (rootModulus h))) =
      rootResidueIndicator h ((P : ZMod (rootModulus h)), (Q : ZMod (rootModulus h))) *
        mixedExtension (fun z => (rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ z : ℂ))
          ((P : ZMod (rootModulus h)), (Q : ZMod (rootModulus h))) := by
  have hp : (P.toNat : ZMod (rootModulus h)) = (P : ZMod (rootModulus h)) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hP]
  have hq : (Q.toNat : ZMod (rootModulus h)) = (Q : ZMod (rootModulus h)) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hQ]
  simpa only [hp, hq] using diagonalSmallMultiplier_mul_rootResidueIndicator
    d h outerU xs hslots D P₀ q₀ P.toNat Q.toNat v hu₀

end Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier

end

end OAI
