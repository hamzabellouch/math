import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseContext

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkProducts Characters FrequencyExposure HistorySignedDecode HistoryFrequencyResidues

theorem exposureStep_matches_signed_static
    {l : ℕ}
    {a a' : State} {u hp hm u' hp' hm' : List SmallSlot}
    {left right left' right' : History l}
    (hs : a.frequency≠0)
    (hs' : a'.frequency≠0)
    (K R : ℕ) (hl : l<K) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (path : List Bool)
    (g g' : KnownGiants R)
    (Xp Xm Xp' Xm' : ℤ)
    (hg : SignedGiantsMatch R (l+1) g Xp Xm) (hg' : SignedGiantsMatch R (l+1) g' Xp' Xm')
    (hdiv : a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣
      reversalNumerator left.root.frequency right.root.frequency
        (Xp*((hp.map SmallSlot.value).prod:ℤ)) (Xm*((hm.map SmallSlot.value).prod:ℤ)))
    (hdiv' : a'.frequency*((u'.map SmallSlot.value).prod:ℤ) ∣
      reversalNumerator left'.root.frequency right'.root.frequency
        (Xp'*((hp'.map SmallSlot.value).prod:ℤ)) (Xm'*((hm'.map SmallSlot.value).prod:ℤ)))
    (hds : (d path).s=a.frequency) (hds' : (d path).s'=a'.frequency)
    (hdv : (d path).v=left.root.frequency) (hdw : (d path).w=right.root.frequency)
    (hdv' : (d path).v'=left'.root.frequency) (hdw' : (d path).w'=right'.root.frequency)
    (hff : (f path).1=⟨fixedProduct hp,fixedProduct hm,(u.map SmallSlot.value).prod⟩)
    (hff' : (f path).2=⟨fixedProduct hp',fixedProduct hm',(u'.map SmallSlot.value).prod⟩)
    (hu : Nat.Coprime (u.map SmallSlot.value).prod R)
    (hu' : Nat.Coprime (u'.map SmallSlot.value).prod R)
    (x y : (ZMod (R^(K+2)))ˣ)
    (hx : (x:ZMod (R^(K+2)))=(bulkProduct hp:ZMod (R^(K+2))))
    (hy : (y:ZMod (R^(K+2)))=(bulkProduct hm:ZMod (R^(K+2))))
    (hx' : (x:ZMod (R^(K+2)))=(bulkProduct hp':ZMod (R^(K+2))))
    (hy' : (y:ZMod (R^(K+2)))=(bulkProduct hm':ZMod (R^(K+2))))
    (b : Bool) :
    let c := exposureStep K R d f b path (l+1,g,g') (x*y) x
    c.1=l ∧ SignedGiantsMatch R l c.2.1
      (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ left.root.frequency right.root.frequency u hp hm)
      (if b then Xm else Xp) ∧ SignedGiantsMatch R l c.2.2
      (signedPivot ⟨a'.frequency,Xp',Xm',a'.small⟩ left'.root.frequency right'.root.frequency u' hp' hm')
      (if b then Xm' else Xp') := by
  let red := ZMod.castHom (pow_dvd_pow R (by omega : l+3≤K+2)) (ZMod (R^(l+3)))
  have hxR : red (x:ZMod (R^(K+2)))=(bulkProduct hp:ZMod (R^(l+3))) := by
    rw [hx]
    exact map_natCast red _
  have hyR : red (y:ZMod (R^(K+2)))=(bulkProduct hm:ZMod (R^(l+3))) := by
    rw [hy]
    exact map_natCast red _
  have hxR' : red (x:ZMod (R^(K+2)))=(bulkProduct hp':ZMod (R^(l+3))) := by
    rw [hx']
    exact map_natCast red _
  have hyR' : red (y:ZMod (R^(K+2)))=(bulkProduct hm':ZMod (R^(l+3))) := by
    rw [hy']
    exact map_natCast red _
  have hf : a.frequency.natAbs∣R := hds ▸ (d path).divides
  have hf' : a'.frequency.natAbs∣R := hds' ▸ (d path).divides'
  have hchild := childGiants_matches_signed_static hs R l hf hu g Xp Xm hg hdiv _ _ hxR hyR b
  have hchild' := childGiants_matches_signed_static hs' R l hf' hu' g' Xp' Xm' hg' hdiv' _ _ hxR' hyR' b
  simp only [exposureStep,Nat.add_sub_cancel,dite_eq_left hl,inv_mul_cancel_left,
    hds,hds',hdv,hdw,hdv',hdw',hff,hff',true_and]
  exact ⟨hchild,hchild'⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
