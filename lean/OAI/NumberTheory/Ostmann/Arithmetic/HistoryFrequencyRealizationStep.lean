import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyConstraint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyLeaves

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters FrequencyExposure

theorem supported_known_rawSplit_of_eq
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (hsize : ∀q∈a.small,V (l+1)<q.value)
    (R K j : ℕ) (s : ℤ) (hf : s.natAbs∣R) (he : s=a.frequency)
    (g : KnownGiants R) (hg : GiantsMatch R j g a)
    (x y : (ZMod (R^(K+2)))ˣ)
    (hx : (bulkProduct hp:ZMod (R^(K+2)))=x)
    (hy : (bulkProduct hm:ZMod (R^(K+2)))=y) :
    rawSplitConstraint s.natAbs left.root.frequency right.root.frequency
      (knownCoefficient R j s hf (fixedProduct hp) (g j).1)
      (knownCoefficient R j s hf (fixedProduct hm) (g j).2)
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) (x*y))
      (ZMod.unitsMap (Template.frequency_dvd_precision R K hf) x) := by
  subst s
  exact supported_known_rawSplit hs hsize R K j hf g hg x y hx hy

theorem exposureStep_matches_actual
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a a' : State} {p p' : ℕ} {u hp hm u' hp' hm' : List SmallSlot}
    {left right left' right' : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hs' : (History.node a' p' u' hp' hm' left' right').Supported V outside)
    (K R : ℕ) (hl : l<K) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (path : List Bool)
    (g g' : KnownGiants R)
    (hg : GiantsMatch R (l+1) g a) (hg' : GiantsMatch R (l+1) g' a')
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
    c.1=l ∧ GiantsMatch R l c.2.1 (if b then right.root else left.root) ∧
      GiantsMatch R l c.2.2 (if b then right'.root else left'.root) := by
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
  have hchild := childGiants_matches hs R l hf hu g hg _ _ hxR hyR b
  have hchild' := childGiants_matches hs' R l hf' hu' g' hg' _ _ hxR' hyR' b
  simp only [exposureStep,Nat.add_sub_cancel,dite_eq_left hl,inv_mul_cancel_left,
    hds,hds',hdv,hdw,hdv',hdw',hff,hff',true_and]
  exact ⟨hchild,hchild'⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
