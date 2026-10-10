import OAI.NumberTheory.Ostmann.Characters.TemplateAdaptedProducts

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem installWords_map {R S:Type*} [Monoid R] [Monoid S] (f:R→*S)
    (k j:ℕ) (C:(schedule k j).Slot→R) (z:WordSlot k j→R) :
    (fun i=>f (installWords k j C z i))=
      installWords k j (fun i=>f (C i)) (fun i=>f (z i)) := by
  funext i
  unfold installWords
  split_ifs <;> simp only [map_mul,map_one]

def knownChild (N M:ℕ) (hMN:M∣N) (k j:ℕ) (b:Bool) (s v w:ℤ)
    (C:(schedule k (j+1)).Slot→ZMod N) (XL XR:ZMod N) : (schedule k j).Slot→ZMod M :=
  coordinateChild k j b (fun i=>ZMod.castHom hMN (ZMod M) (C i))
    (ResidueDivision.divideResidue N M s
      ((v:ZMod N)*blockProduct k j false C*XR-(w:ZMod N)*blockProduct k j true C*XL))

theorem knownChild_actual (N M:ℕ) (hMN:M∣N) (k j:ℕ) (b:Bool) (s v w:ℤ)
    (C:(schedule k (j+1)).Slot→ℤ) (z:WordSlot k (j+1)→ℤ)
    (hs:s≠0) (hNM:s.natAbs*M∣N)
    (hint:s∣v*copiedProduct k j false (installWords k (j+1) C z)-
      w*copiedProduct k j true (installWords k (j+1) C z)) :
    knownChild N M hMN k j b s v w (fun i=>(C i:ZMod N))
      ((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod N)
      ((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod N)=
      fun i=>(coordinateChild (R:=ℤ) k j b C
        (reconstructedPivot k j (installWords k (j+1) C z) s v w) i:ZMod M) := by
  have hn : ((v*copiedProduct k j false (installWords k (j+1) C z)-
      w*copiedProduct k j true (installWords k (j+1) C z):ℤ):ZMod N)=
      (v:ZMod N)*blockProduct k j false (fun i=>(C i:ZMod N))*
        ((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod N)-
      (w:ZMod N)*blockProduct k j true (fun i=>(C i:ZMod N))*
        ((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod N) := by
    change ((v*blockProduct k j false (installWords k (j+1) C z)-
      w*blockProduct k j true (installWords k (j+1) C z):ℤ):ZMod N)=_
    rw [blockProduct_installWords,blockProduct_installWords]
    simp only [Int.cast_sub,Int.cast_mul,blockProduct,Int.cast_prod,mul_assoc]
  unfold knownChild
  simp only [map_intCast]
  rw [← hn,ResidueDivision.divideResidue_intCast N M s _ hs hNM hint]
  exact (coordinateChild_map (fun x:ℤ=>(x:ZMod M)) k j b C
    (reconstructedPivot k j (installWords k (j+1) C z) s v w)).symm

theorem childState_installWords_residue (N M:ℕ) (hMN:M∣N) (k j:ℕ) (b:Bool) (s v w:ℤ)
    (C:(schedule k (j+1)).Slot→ℤ) (z:WordSlot k (j+1)→ℤ)
    (hs:s≠0) (hNM:s.natAbs*M∣N)
    (hint:s∣v*copiedProduct k j false (installWords k (j+1) C z)-
      w*copiedProduct k j true (installWords k (j+1) C z)) :
    (fun i=>(childState k j b (installWords k (j+1) C z)
      (reconstructedPivot k j (installWords k (j+1) C z) s v w) i:ZMod M))=
      installWords k j
        (knownChild N M hMN k j b s v w (fun i=>(C i:ZMod N))
          ((∏i:WordSlot k j,splitWords k j true z i:ℤ):ZMod N)
          ((∏i:WordSlot k j,splitWords k j false z i:ℤ):ZMod N))
        (fun i=>((splitWords (R:=ℤ) k j b z i:ℤ):ZMod M)) := by
  rw [knownChild_actual N M hMN k j b s v w C z hs hNM hint]
  change (fun i=>((coordinateChild k j b (installWords k (j+1) C z)
    (reconstructedPivot k j (installWords k (j+1) C z) s v w) i:ℤ):ZMod M))=_
  rw [coordinateChild_installWords]
  exact installWords_map (Int.castRingHom (ZMod M)).toMonoidHom k j _ _

end Ostmann.Characters.Template

end

end OAI
