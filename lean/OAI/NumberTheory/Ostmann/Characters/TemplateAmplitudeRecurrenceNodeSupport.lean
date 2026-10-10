import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagationActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem CurrentAtomSupport.source_pivot_pos {k j : ℕ} (hj : j < k)
    {P s : ℤ} {h : CopiedState k j} {y : OutsideState k j}
    (hs : CurrentAtomSupport k j s (sourceState k j P h y)) : 0 < P := by
  have hp := hs.positive (pivotSlot k j hj).val
  simpa only [sourceState,childState_pivot k j true _ _ _ (pivotSlot k j hj).property]
    using hp

theorem CurrentAtomSupport.source_pivot_coprime {k j : ℕ} (hj : j < k)
    {P s : ℤ} {h : CopiedState k j} {y : OutsideState k j}
    (hs : CurrentAtomSupport k j s (sourceState k j P h y)) : IsCoprime s P := by
  have hp := hs.root_coprime (pivotSlot k j hj).val
  simpa only [sourceState,childState_pivot k j true _ _ _ (pivotSlot k j hj).property]
    using hp

theorem CurrentAtomSupport.copiedProduct_coprime {k j : ℕ} {s : ℤ}
    {x : State k (j+1)} (hs : CurrentAtomSupport k (j+1) s x) (b : Bool) :
    IsCoprime s (copiedProduct k j b x) := by
  apply IsCoprime.prod_right
  intro i hi
  exact hs.root_coprime (.inl (i,b))

theorem CurrentAtomSupport.copiedProduct_unit {k j : ℕ} {s : ℤ}
    {x : State k (j+1)} (hs : CurrentAtomSupport k (j+1) s x) (b : Bool) :
    IsUnit (copiedProduct k j b x : ZMod s.natAbs) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  simpa only [Int.natCast_natAbs] using (hs.copiedProduct_coprime b).abs_left

theorem reconstructedPivot_pairedState_of_reversal {k j : ℕ}
    {P s v w : ℤ} {hL hR : CopiedState k j} {y : OutsideState k j}
    (hs : s ≠ 0) (he : v*(∏i,hR i)-w*(∏i,hL i)=s*P) :
    reconstructedPivot k j (pairedState k j hL hR y) s v w = P := by
  simp only [reconstructedPivot,copiedProduct_pairedState,ite_true,Bool.false_eq_true,ite_false]
  rw [he,Int.mul_ediv_cancel_left _ hs]

theorem nodeSupports_pairedState_of_reversal {k j : ℕ} (hj : j < k)
    {P s v w B V : ℤ} {hL hR : CopiedState k j} {y : OutsideState k j}
    (hl : CurrentAtomSupport k j v (sourceState k j P hL y))
    (hr : CurrentAtomSupport k j w (sourceState k j P hR y))
    (hn : CurrentAtomSupport k (j+1) s (pairedState k j hL hR y))
    (he : v*(∏i,hR i)-w*(∏i,hL i)=s*P)
    (hPB : P ≤ B) (hv : |v| ≤ V) (hw : |w| ≤ V)
    (hgap : 2*B*V < ∏i,hR i) :
    NodeSupported k j (pairedState k j hL hR y) s v w B V ∧
      IntegerNodeSupport k j s v w (pairedState k j hL hR y) := by
  have hP := reconstructedPivot_pairedState_of_reversal (y := y) hn.root_ne_zero he
  have hright : 0 < copiedProduct k j false (pairedState k j hL hR y) := by
    change 0 < ∏i,hR i
    exact Finset.prod_pos (fun i hi => hr.copied_pos i)
  have hi : s ∣ v*copiedProduct k j false (pairedState k j hL hR y)-
      w*copiedProduct k j true (pairedState k j hL hR y) := by
    change s ∣ v*(∏i,hR i)-w*(∏i,hL i)
    rw [he]
    exact dvd_mul_right s P
  refine ⟨⟨hn.root_ne_zero,hright,?_,?_,hv,hw,hgap,hi,
    hn.copiedProduct_coprime false,?_⟩,⟨hi,hn.copiedProduct_unit true,
    hn.copiedProduct_unit false⟩⟩
  · rw [hP]
    exact hl.source_pivot_pos hj
  · rw [hP]
    exact hPB
  · rw [hP]
    exact (hr.source_pivot_coprime hj).symm

end Ostmann.Characters.Template

end

end OAI
