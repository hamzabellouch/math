import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyConstraint
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyContext

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters
open Characters.Template (unitConvention unitConvention_coe)

def signedCoefficientUnit (s X : ℤ) (xs : List SmallSlot) : (ZMod s.natAbs)ˣ :=
  unitConvention ((X:ZMod s.natAbs)*(fixedProduct xs:ZMod s.natAbs))

theorem signedCoefficientUnit_coe (s X : ℤ) (xs : List SmallSlot)
    (hX : IsUnit (X:ZMod s.natAbs))
    (hc : ∀ q∈xs,Nat.Coprime q.value s.natAbs) :
    (signedCoefficientUnit s X xs:ZMod s.natAbs)=
      (X:ZMod s.natAbs)*(fixedProduct xs:ZMod s.natAbs) := by
  exact unitConvention_coe _ (hX.mul
    ((ZMod.isUnit_iff_coprime _ _).mpr (fixedProduct_coprime hc)))

theorem signed_rawSplit_iff (s v w Xp Xm : ℤ) (hp hm : List SmallSlot)
    (hXp : IsUnit (Xp:ZMod s.natAbs)) (hXm : IsUnit (Xm:ZMod s.natAbs))
    (hhp : ∀ q∈hp,Nat.Coprime q.value s.natAbs)
    (hhm : ∀ q∈hm,Nat.Coprime q.value s.natAbs) :
    rawSplitConstraint s.natAbs v w (signedCoefficientUnit s Xp hp)
      (signedCoefficientUnit s Xm hm) (bulkUnit s hp*bulkUnit s hm) (bulkUnit s hp) ↔
      s ∣ reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ)) := by
  have hz : (((reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
      (Xm*((hm.map SmallSlot.value).prod:ℤ))):ℤ):ZMod s.natAbs)=0 ↔
      s ∣ reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ)) := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd,Int.natCast_natAbs,abs_dvd]
  rw [←hz]
  unfold rawSplitConstraint
  rw [mul_div_cancel_left,signedCoefficientUnit_coe s Xp hp hXp hhp,
    signedCoefficientUnit_coe s Xm hm hXm hhm,bulkUnit_coe s hp hhp,bulkUnit_coe s hm hhm]
  simp only [reversalNumerator,product_split,Int.cast_sub,Int.cast_mul,Int.cast_natCast,
    Nat.cast_mul,mul_assoc,sub_eq_zero]

theorem knownCoefficient_intCast (R j : ℕ) (s : ℤ) (hs : s.natAbs∣R)
    (fixed : ℕ) (X : ℤ) :
    knownCoefficient R j s hs fixed (X:ZMod (R^(j+2)))=
      unitConvention ((X:ZMod s.natAbs)*(fixed:ZMod s.natAbs)) := by
  simp only [knownCoefficient,map_intCast]

theorem signed_known_rawSplit_iff (s v w Xp Xm : ℤ) (hp hm : List SmallSlot)
    (R K j : ℕ) (hf : s.natAbs∣R) (g : KnownGiants R)
    (hg : SignedGiantsMatch R j g Xp Xm)
    (x y : (ZMod (R^(K+2)))ˣ)
    (hx : (bulkProduct hp:ZMod (R^(K+2)))=x)
    (hy : (bulkProduct hm:ZMod (R^(K+2)))=y)
    (hXp : IsUnit (Xp:ZMod s.natAbs)) (hXm : IsUnit (Xm:ZMod s.natAbs))
    (hhp : ∀ q∈hp,Nat.Coprime q.value s.natAbs)
    (hhm : ∀ q∈hm,Nat.Coprime q.value s.natAbs) :
    rawSplitConstraint s.natAbs v w
      (knownCoefficient R j s hf (fixedProduct hp) (g j).1)
      (knownCoefficient R j s hf (fixedProduct hm) (g j).2)
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) (x*y))
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) x) ↔
      s ∣ reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ)) := by
  rw [hg.1,hg.2,knownCoefficient_intCast,knownCoefficient_intCast,map_mul]
  have hL := unitConvention_natCast_map s.natAbs (R^(K+2))
    (Template.frequency_dvd_precision R K hf) (bulkProduct hp) x hx
  have hR := unitConvention_natCast_map s.natAbs (R^(K+2))
    (Template.frequency_dvd_precision R K hf) (bulkProduct hm) y hy
  simpa only [signedCoefficientUnit,bulkUnit,hL,hR] using
    signed_rawSplit_iff s v w Xp Xm hp hm hXp hXm hhp hhm

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
