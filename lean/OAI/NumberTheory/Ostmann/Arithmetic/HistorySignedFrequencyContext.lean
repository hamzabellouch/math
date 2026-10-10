import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyContext
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeRebuild

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters HistorySignedDecode
open Characters.Template (unitConvention unitConvention_coe)
open Characters.ResidueDivision

def SignedGiantsMatch (R j : ℕ) (g : KnownGiants R) (Xp Xm : ℤ) : Prop :=
  (g j).1=(Xp:ZMod (R^(j+2))) ∧ (g j).2=(Xm:ZMod (R^(j+2)))

def signedInitialGiants (R : ℕ) (Xp Xm : ℤ) : KnownGiants R := fun _ => (Xp,Xm)

@[simp] theorem signedInitialGiants_matches (R j : ℕ) (Xp Xm : ℤ) :
    SignedGiantsMatch R j (signedInitialGiants R Xp Xm) Xp Xm := ⟨rfl,rfl⟩

theorem nodePivot_eq_signed (N M : ℕ) (s v w Xp Xm : ℤ) (Hp Hm U : ℕ)
    (p : ℤ) (u : (ZMod M)ˣ) (hu : (U:ZMod M)=u) (hs : s≠0)
    (hNM : s.natAbs*M∣N)
    (hrev : reversalNumerator v w (Xp*(Hp:ℤ)) (Xm*(Hm:ℤ))=s*(U:ℤ)*p) :
    nodePivot N M s v w (Xp:ZMod N) (Xm:ZMod N) Hp Hm u=(p:ZMod M) := by
  have he := unitDivideResidue_reversal N M s (U:ℤ) v w (Xp*(Hp:ℤ))
    (Xm*(Hm:ℤ)) p u (by simpa only [Int.cast_natCast] using hu) hs hNM hrev.symm
  simpa only [nodePivot,Int.cast_natCast,Int.cast_mul] using he

theorem childGiants_matches_signed {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
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
    (History.supported_root_frequency_ne_zero hs)
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

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
