import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallAverageActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic
open Construction

namespace DiagonalSmallResidueNorm

theorem SmallUnitData.changeGiants {D P₀ q₀ : ℕ} {outerU xs : List SmallSlot} {v : ℤ}
    (hu : SmallUnitData D P₀ q₀ outerU xs v) (P q : ℕ)
    (hq : ∀i,IsUnit (q:ZMod (smallPrime xs outerU i)))
    (hP : ∀i : Fin outerU.length,IsUnit (P:ZMod outerU[i].value)) :
    SmallUnitData D P q outerU xs v where
  frequency := hu.frequency
  denominator := hu.denominator
  giant := hq
  outer := hP
  coprime := hu.coprime

end DiagonalSmallResidueNorm
namespace HistoryDiagonalSmallAverage
open DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration

theorem rootSmallTest_independent_giants (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (hu : SmallUnitData D P q outerU xs v) :
    rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀ =
      rootSmallTest d h outerU xs hslots D P q v hu := rfl

theorem actualRootDraw_fst_natCast {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) (hu : SmallUnitData D P q outerU xs v) :
    (actualRootDraw h outerU xs hslots D P q v hu).1=(P:ZMod (rootModulus h)) := by
  change (ZMod.ringEquivCongr (small_modulus_eq_root h outerU xs hslots).symm).symm
    (P:ZMod (∏i,smallPrime xs outerU i)) = _
  exact map_natCast _ _

theorem actualRootDraw_snd_coe_natCast {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P q : ℕ) (v : ℤ) (hu : SmallUnitData D P q outerU xs v) :
    ((actualRootDraw h outerU xs hslots D P q v hu).2:ZMod (rootModulus h))=
      (q:ZMod (rootModulus h)) := by
  change (((Units.mapEquiv (ZMod.ringEquivCongr
    (small_modulus_eq_root h outerU xs hslots).symm).toMulEquiv).symm hu.giantUnit):
      ZMod (rootModulus h)) = _
  change (ZMod.ringEquivCongr (small_modulus_eq_root h outerU xs hslots).symm).symm
    (hu.giantUnit:ZMod (∏i,smallPrime xs outerU i)) = _
  rw [SmallUnitData.giantUnit_coe]
  exact map_natCast _ _

theorem rootSmallTest_reference_actualRootDraw (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v) (hu : SmallUnitData D P q outerU xs v) :
    rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀
      (actualRootDraw h outerU xs hslots D P q v hu)=
        diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs := by
  rw [rootSmallTest_independent_giants d h outerU xs hslots D P₀ q₀ P q v hu₀ hu]
  exact rootSmallTest_actualRootDraw d h outerU xs hslots D P q v hu

theorem rootSmallTest_changeGiants_actualRootDraw (d : Decomposition) {l : ℕ} (h : History l)
    (outerU xs : List SmallSlot) (hslots : h.root.small.Perm (outerU++xs))
    (D P₀ q₀ P q : ℕ) (v : ℤ) [∀i,Fact (smallPrime xs outerU i).Prime]
    (hu₀ : SmallUnitData D P₀ q₀ outerU xs v)
    (hq : ∀i,IsUnit (q:ZMod (smallPrime xs outerU i)))
    (hP : ∀i : Fin outerU.length,IsUnit (P:ZMod outerU[i].value)) :
    rootSmallTest d h outerU xs hslots D P₀ q₀ v hu₀
      (actualRootDraw h outerU xs hslots D P q v (hu₀.changeGiants P q hq hP))=
        diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs :=
  rootSmallTest_reference_actualRootDraw d h outerU xs hslots D P₀ q₀ P q v hu₀
    (hu₀.changeGiants P q hq hP)

end HistoryDiagonalSmallAverage
end Ostmann.Arithmetic

end

end OAI
