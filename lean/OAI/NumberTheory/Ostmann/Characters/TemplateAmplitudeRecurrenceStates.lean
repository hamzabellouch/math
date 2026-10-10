import OAI.NumberTheory.Ostmann.Characters.TemplateWeight

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

abbrev CopiedState (k j : ℕ) := {i:(schedule k j).Slot // (schedule k j).IsCopied j i} → ℤ
abbrev OutsideState (k j : ℕ) := {i:(schedule k j).Slot // (schedule k j).IsOutside j i} → ℤ

def pairedState (k j : ℕ) (hL hR : CopiedState k j) (y : OutsideState k j) : State k (j+1)
  | .inl (i,b) => if b then hL i else hR i
  | .inr i => y i

def sourceState (k j : ℕ) (P : ℤ) (h : CopiedState k j) (y : OutsideState k j) : State k j :=
  childState k j true (pairedState k j h h y) P

theorem childState_pairedState (k j : ℕ) (b : Bool) (P : ℤ)
    (hL hR : CopiedState k j) (y : OutsideState k j) :
    childState k j b (pairedState k j hL hR y) P =
      sourceState k j P (if b then hL else hR) y := by
  unfold sourceState
  cases b <;> funext i <;> simp only [Bool.false_eq_true,ite_false,ite_true,childState]
  all_goals split_ifs <;> rfl

@[simp] theorem copiedProduct_pairedState (k j : ℕ) (b : Bool)
    (hL hR : CopiedState k j) (y : OutsideState k j) :
    copiedProduct k j b (pairedState k j hL hR y) = ∏ i, (if b then hL else hR) i := by
  cases b <;> rfl

@[simp] theorem outsideProduct_pairedState (k j : ℕ)
    (hL hR : CopiedState k j) (y : OutsideState k j) :
    outsideProduct k j (pairedState k j hL hR y) = ∏ i, y i := rfl

theorem weight_pairedState (k j : ℕ) (mask : (j:ℕ) → ℤ → State k j → Prop)
    (X Δ W : ℝ) (hL hR : CopiedState k j) (y : OutsideState k j)
    (s v w : ℤ) (tL tR : HistoryReconstruction.Tree j) :
    weight k mask X Δ W (j+1) s (pairedState k j hL hR y) ((v,w),tL,tR) =
      if mask (j+1) s (pairedState k j hL hR y) then
        let P := (v*(∏i,hR i)-w*(∏i,hL i))/s
        weight k mask X Δ W j v (sourceState k j P hL y) tL *
          star (weight k mask X Δ W j w (sourceState k j P hR y) tR)
      else 0 := by
  simp only [weight,reconstructedPivot,copiedProduct_pairedState,childState_pairedState,
    ite_true,Bool.false_eq_true,ite_false]
  rfl

end Ostmann.Characters.Template

end

end OAI
