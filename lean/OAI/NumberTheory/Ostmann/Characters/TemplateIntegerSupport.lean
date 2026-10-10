import OAI.NumberTheory.Ostmann.Characters.TemplateArithmeticSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open FrequencyExposure
attribute [local instance] Classical.propDecidable

structure IntegerNodeSupport (k j:ℕ) (s v w:ℤ) (x:State k (j+1)) : Prop where
  integral : s∣v*copiedProduct k j false x-w*copiedProduct k j true x
  left_unit : IsUnit (copiedProduct k j true x:ZMod s.natAbs)
  right_unit : IsUnit (copiedProduct k j false x:ZMod s.natAbs)

@[reducible] def IntegerSupport (k R:ℕ) (d:List Bool→Data R) :
    (j:ℕ)→List Bool→State k j→State k j→Prop
  | 0,_,_,_ => True
  | j+1,p,x,x' => IntegerNodeSupport k j (d p).s (d p).v (d p).w x ∧
      IntegerNodeSupport k j (d p).s' (d p).v' (d p).w' x' ∧
      IntegerSupport k R d j (false::p)
        (childState k j true x (reconstructedPivot k j x (d p).s (d p).v (d p).w))
        (childState k j true x' (reconstructedPivot k j x' (d p).s' (d p).v' (d p).w')) ∧
      IntegerSupport k R d j (true::p)
        (childState k j false x (reconstructedPivot k j x (d p).s (d p).v (d p).w))
        (childState k j false x' (reconstructedPivot k j x' (d p).s' (d p).v' (d p).w'))

theorem known_block_isUnit (k j:ℕ) (b:Bool) (s:ℤ)
    (C:State k (j+1)) (z:WordSlot k (j+1)→ℤ)
    (h:IsUnit (copiedProduct k j b (installWords k (j+1) C z):ZMod s.natAbs)) :
    IsUnit (blockProduct k j b (fun i=>(C i:ZMod s.natAbs))) := by
  change IsUnit ((blockProduct k j b (installWords k (j+1) C z):ℤ):ZMod s.natAbs) at h
  rw [blockProduct_installWords,Int.cast_mul] at h
  have hc := (Commute.all _ _).isUnit_mul_iff.mp h
  simpa only [blockProduct,Int.cast_prod] using hc.1

theorem integerSupport_implies_arithmeticSupport (k R:ℕ) (d:List Bool→Data R)
    (j:ℕ) (p:List Bool) (C C':State k j) (z:WordSlot k j→ℤ)
    (h:IntegerSupport k R d j p (installWords k j C z) (installWords k j C' z)) :
    ArithmeticSupport k R d j p C C' z := by
  induction j generalizing p with
  | zero => trivial
  | succ j ih =>
    refine ⟨⟨h.1.integral,h.2.1.integral,
      known_block_isUnit k j true _ C z h.1.left_unit,
      known_block_isUnit k j false _ C z h.1.right_unit,
      known_block_isUnit k j true _ C' z h.2.1.left_unit,
      known_block_isUnit k j false _ C' z h.2.1.right_unit⟩,?_,?_⟩
    · apply ih (false::p)
      convert h.2.2.1 using 1 <;>
        exact (coordinateChild_installWords k j true _ _ _).symm
    · apply ih (true::p)
      convert h.2.2.2 using 1 <;>
        exact (coordinateChild_installWords k j false _ _ _).symm

end Ostmann.Characters.Template

end

end OAI
