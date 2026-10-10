import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeleton

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkProducts HistoryFrequencyResidues Characters HistorySignedDecode
open Characters.Template (unitConvention unitConvention_coe)
open Characters.ResidueDivision

theorem childGiants_matches_signed_static {l : ℕ}
    {a : State} {comp hp hm : List SmallSlot} {left right : History l}
    (hfreq : a.frequency≠0)
    (R j : ℕ) (hf : a.frequency.natAbs∣R)
    (hu : Nat.Coprime (comp.map SmallSlot.value).prod R)
    (g : KnownGiants R) (Xp Xm : ℤ) (hg : SignedGiantsMatch R (j+1) g Xp Xm)
    (hdiv : a.frequency*((comp.map SmallSlot.value).prod:ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp*((hp.map SmallSlot.value).prod:ℤ)) (Xm*((hm.map SmallSlot.value).prod:ℤ)))
    (XL XR : ZMod (R^(j+3)))
    (hXL : XL=(bulkProduct hp:ZMod (R^(j+3))))
    (hXR : XR=(bulkProduct hm:ZMod (R^(j+3)))) (b : Bool) :
    SignedGiantsMatch R j
      (childGiants R j a.frequency left.root.frequency right.root.frequency
        (fixedProduct hp) (fixedProduct hm) (comp.map SmallSlot.value).prod g XL XR b)
      (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency comp hp hm)
      (if b then Xm else Xp) := by
  have hU : IsUnit ((comp.map SmallSlot.value).prod:ZMod (R^(j+2))) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hu.pow_right _)
  have hunit : ((comp.map SmallSlot.value).prod:ZMod (R^(j+2)))=
      unitConvention ((comp.map SmallSlot.value).prod:ZMod (R^(j+2))) :=
    (unitConvention_coe _ hU).symm
  have hrev : reversalNumerator left.root.frequency right.root.frequency
      (Xp*((hp.map SmallSlot.value).prod:ℤ)) (Xm*((hm.map SmallSlot.value).prod:ℤ))=
      a.frequency*((comp.map SmallSlot.value).prod:ℤ)*
        signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency comp hp hm :=
    (Int.mul_ediv_cancel' hdiv).symm
  have hP := nodePivot_eq_signed (R^(j+3)) (R^(j+2)) a.frequency
    left.root.frequency right.root.frequency Xp Xm _ _ _ _
    (unitConvention ((comp.map SmallSlot.value).prod:ZMod (R^(j+2)))) hunit
    hfreq
    (frequency_power_divides R a.frequency hf (j+2)) hrev
  have hx (xs : List SmallSlot) :
      (fixedProduct xs:ZMod (R^(j+3)))*(bulkProduct xs:ZMod (R^(j+3)))=
        ((xs.map SmallSlot.value).prod:ZMod (R^(j+3))) := by
    rw [product_split,Nat.cast_mul]
  cases b <;> constructor <;>
    simp only [childGiants,Function.update_self,Bool.false_eq_true,
      ite_false,ite_true,hg.1,hg.2,hXL,hXR,hx,map_intCast]
  · exact hP
  · exact hP

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
