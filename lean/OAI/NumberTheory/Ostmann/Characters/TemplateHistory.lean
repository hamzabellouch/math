import OAI.NumberTheory.Ostmann.Characters.HistoryReconstruction
import OAI.NumberTheory.Ostmann.Characters.TemplateSchedule

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

abbrev State (k j:ℕ) := (schedule k j).Slot → ℤ

def copiedProduct (k j:ℕ) (b:Bool) (x:State k (j+1)) : ℤ :=
  ∏i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}, x (.inl (i,b))

def reconstructedPivot (k j:ℕ) (x:State k (j+1)) (s v w:ℤ) : ℤ :=
  (v*copiedProduct k j false x-w*copiedProduct k j true x)/s

def childState (k j:ℕ) (b:Bool) (x:State k (j+1)) (P:ℤ) : State k j := fun i=>
  if hp:(schedule k j).IsPivot j i then P
  else if hc:(schedule k j).IsCopied j i then x (.inl (⟨i,hc⟩,b))
  else x (.inr ⟨i,⟨hp,hc⟩⟩)

theorem childState_pivot (k j:ℕ) (b:Bool) (x:State k (j+1)) (P:ℤ)
    (i:(schedule k j).Slot) (hi:(schedule k j).IsPivot j i) :
    childState k j b x P i=P := by simp only [childState,dite_eq_left hi]

theorem childState_copied (k j:ℕ) (b:Bool) (x:State k (j+1)) (P:ℤ)
    (i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i}) :
    childState k j b x P i.val=x (.inl (i,b)) := by
  have hn : ¬(schedule k j).IsPivot j i.val := fun h=>
    pivot_not_copied _ _ _ h i.property
  simp only [childState,dite_eq_right hn,dite_eq_left i.property]

theorem childState_outside (k j:ℕ) (b:Bool) (x:State k (j+1)) (P:ℤ)
    (i:{i:(schedule k j).Slot // (schedule k j).IsOutside j i}) :
    childState k j b x P i.val=x (.inr i) := by
  simp only [childState,dite_eq_right i.property.1,dite_eq_right i.property.2]

structure NodeSupported (k j:ℕ) (x:State k (j+1)) (s v w B V:ℤ) : Prop where
  root_ne_zero : s≠0
  right_pos : 0<copiedProduct k j false x
  pivot_pos : 0<reconstructedPivot k j x s v w
  pivot_le : reconstructedPivot k j x s v w≤B
  left_frequency_le : |v|≤V
  right_frequency_le : |w|≤V
  range_gap : 2*B*V<copiedProduct k j false x
  integral : s∣v*copiedProduct k j false x-w*copiedProduct k j true x
  root_unit : IsCoprime s (copiedProduct k j false x)
  pivot_unit : IsCoprime (reconstructedPivot k j x s v w) w

theorem NodeSupported.unique {k j:ℕ} {x:State k (j+1)} {s v w v' w' B V:ℤ}
    (h:NodeSupported k j x s v w B V) (h':NodeSupported k j x s v' w' B V) :
    v=v' ∧ w=w' := by
  have he : v*copiedProduct k j false x-w*copiedProduct k j true x=
      s*reconstructedPivot k j x s v w := (Int.mul_ediv_cancel' h.integral).symm
  have he' : v'*copiedProduct k j false x-w'*copiedProduct k j true x=
      s*reconstructedPivot k j x s v' w' := (Int.mul_ediv_cancel' h'.integral).symm
  exact (reversal_unique_of_range he he' h.root_ne_zero h.right_pos
    h.pivot_pos h'.pivot_pos h.pivot_le h'.pivot_le h.right_frequency_le h'.right_frequency_le
    h.range_gap h.root_unit h.pivot_unit h'.pivot_unit).imp_right (fun hh=>hh.1)

@[reducible] def Supported (k:ℕ) (B V:(j:ℕ)→State k (j+1)→ℤ) :
    (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,_,_ => True
  | j+1,s,x,t =>
      NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x) ∧
      Supported k B V j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      Supported k B V j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem supported_unique (k:ℕ) (B V:(j:ℕ)→State k (j+1)→ℤ) (j:ℕ)
    (s:ℤ) (x:State k j) (t t':HistoryReconstruction.Tree j)
    (h:Supported k B V j s x t) (h':Supported k B V j s x t') : t=t' := by
  induction j generalizing s with
  | zero => exact Subsingleton.elim _ _
  | succ j ih =>
    rcases t with ⟨⟨v,w⟩,l,r⟩
    rcases t' with ⟨⟨v',w'⟩,l',r'⟩
    obtain ⟨hv,hw⟩ := NodeSupported.unique h.1 h'.1
    change v=v' at hv
    change w=w' at hw
    subst v'
    subst w'
    have hl := ih _ _ l l' h.2.1 h'.2.1
    have hr := ih _ _ r r' h.2.2 h'.2.2
    subst l'
    subst r'
    rfl

def leafStates (k:ℕ) : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j →
    List (ℤ × State k 0)
  | 0,s,x,_ => [(s,x)]
  | j+1,s,x,t =>
    leafStates k j t.1.1 (childState k j true x
      (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ++
    leafStates k j t.1.2 (childState k j false x
      (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem leafStates_length (k j:ℕ) (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j) :
    (leafStates k j s x t).length=2^j := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => simp only [leafStates,List.length_append,ih,pow_succ]; omega

end Ostmann.Characters.Template

end

end OAI
