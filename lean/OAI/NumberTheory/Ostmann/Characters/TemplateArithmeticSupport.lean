import OAI.NumberTheory.Ostmann.Characters.TemplateExposureRealizationStep

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open FrequencyExposure BinaryExposure
attribute [local instance] Classical.propDecidable

structure NodeArithmetic (k j R:ℕ) (d:Data R)
    (C C':(schedule k (j+1)).Slot→ℤ) (z:WordSlot k (j+1)→ℤ) : Prop where
  integral : d.s∣d.v*copiedProduct k j false (installWords k (j+1) C z)-
    d.w*copiedProduct k j true (installWords k (j+1) C z)
  integral' : d.s'∣d.v'*copiedProduct k j false (installWords k (j+1) C' z)-
    d.w'*copiedProduct k j true (installWords k (j+1) C' z)
  left_unit : IsUnit (blockProduct k j true (fun i=>(C i:ZMod d.s.natAbs)))
  right_unit : IsUnit (blockProduct k j false (fun i=>(C i:ZMod d.s.natAbs)))
  left_unit' : IsUnit (blockProduct k j true (fun i=>(C' i:ZMod d.s'.natAbs)))
  right_unit' : IsUnit (blockProduct k j false (fun i=>(C' i:ZMod d.s'.natAbs)))

@[reducible] def ArithmeticSupport (k R:ℕ) (d:List Bool→Data R) :
    (j:ℕ)→List Bool→((schedule k j).Slot→ℤ)→((schedule k j).Slot→ℤ)→(WordSlot k j→ℤ)→Prop
  | 0,_,_,_,_ => True
  | j+1,p,C,C',z => NodeArithmetic k j R (d p) C C' z ∧
      ArithmeticSupport k R d j (false::p)
        (coordinateChild k j true C (reconstructedPivot k j (installWords k (j+1) C z)
          (d p).s (d p).v (d p).w))
        (coordinateChild k j true C' (reconstructedPivot k j (installWords k (j+1) C' z)
          (d p).s' (d p).v' (d p).w')) (splitWords k j true z) ∧
      ArithmeticSupport k R d j (true::p)
        (coordinateChild k j false C (reconstructedPivot k j (installWords k (j+1) C z)
          (d p).s (d p).v (d p).w))
        (coordinateChild k j false C' (reconstructedPivot k j (installWords k (j+1) C' z)
          (d p).s' (d p).v' (d p).w')) (splitWords k j false z)

theorem leafAdmissible_pair {G H:Type*} [Group G] [Fintype G]
    (c:ℕ→H→G→G→Prop) (l r:ℕ→H→G→G→H) (j:ℕ) (h:H)
    (x y:BinaryHaar.Leaves G j) :
    leafAdmissible c l r (j+1) h (x,y) ↔
      c j h (BinaryHaar.product (G:=G) x*BinaryHaar.product (G:=G) y) (BinaryHaar.product (G:=G) x) ∧
      leafAdmissible c l r j
        (l j h (BinaryHaar.product (G:=G) x*BinaryHaar.product (G:=G) y)
          (BinaryHaar.product (G:=G) x)) x ∧
      leafAdmissible c l r j
        (r j h (BinaryHaar.product (G:=G) x*BinaryHaar.product (G:=G) y)
          (BinaryHaar.product (G:=G) x)) y := by
  simp only [leafAdmissible,admissible,BinaryHaar.product,BinaryHaar.expose,
    Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,BinaryHaar.decoratedSplit,Equiv.coe_fn_mk,
    BinaryHaar.expose_first,inv_mul_cancel_left]

theorem arithmeticSupport_implies_leafAdmissible (k K R:ℕ) [NeZero R] (d:List Bool→Data R)
    (j:ℕ) (hj:j≤K) (p:List Bool) (h:PairedKnownStates k R)
    (C C':(schedule k j).Slot→ℤ) (z:WordSlot k j→ℤ)
    (ξ:WordSlot k j→(ZMod (R^(K+2)))ˣ)
    (hξ:∀i,(z i:ZMod (R^(K+2)))=ξ i)
    (hc:ContextMatches k R j h.1 C) (hc':ContextMatches k R j h.2 C')
    (hs:ArithmeticSupport k R d j p C C' z) :
    leafAdmissible (exposureConstraint k K R d)
      (exposureStep k K R d false) (exposureStep k K R d true) j (p,h)
      (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j ξ) := by
  induction j generalizing p h with
  | zero => trivial
  | succ j ih =>
    let XL := BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ)
      (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j true ξ))
    let XR := BinaryHaar.product (G:=(ZMod (R^(K+2)))ˣ)
      (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j false ξ))
    have hrep (b:Bool) (i:WordSlot k j) :
        ((splitWords (R:=ℤ) k j b z i:ℤ):ZMod (R^(K+2)))=splitWords k j b ξ i := hξ _
    have hXL : ((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod (R^(K+2)))=XL := by
      simpa only [ZMod.unitsMap_self,MonoidHom.id_apply] using
        chosen_product_residue (R^(K+2)) (R^(K+2)) k j (dvd_refl _) _ _ (hrep true)
    have hXR : ((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod (R^(K+2)))=
        (XL⁻¹*(XL*XR):(ZMod (R^(K+2)))ˣ) := by
      simpa only [ZMod.unitsMap_self,MonoidHom.id_apply,inv_mul_cancel_left] using
        chosen_product_residue (R^(K+2)) (R^(K+2)) k j (dvd_refl _) _ _ (hrep false)
    have hl := exposureStep_matches k K R j (by omega) d p false h C C' z (XL*XR) XL
      hXL hXR hc hc' hs.1.integral hs.1.integral'
    have hr := exposureStep_matches k K R j (by omega) d p true h C C' z (XL*XR) XL
      hXL hXR hc hc' hs.1.integral hs.1.integral'
    change leafAdmissible _ _ _ (j+1) (p,h)
      (wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j true ξ),
        wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j (splitWords k j false ξ))
    rw [leafAdmissible_pair]
    refine ⟨?_,?_,?_⟩
    · exact realized_node_constraint k K R j d p h C C' z ξ hξ hc hc'
        hs.1.left_unit hs.1.right_unit hs.1.left_unit' hs.1.right_unit' hs.1.integral hs.1.integral'
    · exact ih (by omega) (false::p) (exposureStep k K R d false j (p,h) (XL*XR) XL).2
        _ _ _ (splitWords k j true ξ) (hrep true) hl.1 hl.2 hs.2.1
    · exact ih (by omega) (true::p) (exposureStep k K R d true j (p,h) (XL*XR) XL).2
        _ _ _ (splitWords k j false ξ) (hrep false) hr.1 hr.2 hs.2.2

end Ostmann.Characters.Template

end

end OAI
