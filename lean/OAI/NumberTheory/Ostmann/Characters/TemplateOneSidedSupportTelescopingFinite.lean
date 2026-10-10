import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalPrior

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι α : Type*} [DecidableEq ι]

def hybridSupport (removed : Finset ι) (core : α→Prop)
    (coprime : ι→α→Prop) (polynomial : ι→Prop) (a : α) : Prop :=
  core a ∧ ∀i,if i∈removed then polynomial i else coprime i a

def remainder (removed : Finset ι) (i : ι) (core : α→Prop)
    (coprime : ι→α→Prop) (polynomial : ι→Prop) (a : α) : Prop :=
  core a ∧ ∀q,q≠i → if q∈removed then polynomial q else coprime q a

def hybridValue (removed : Finset ι) (core : α→Prop)
    (coprime : ι→α→Prop) (polynomial : ι→Prop) (f : α→ℂ) (a : α) : ℂ :=
  if hybridSupport removed core coprime polynomial a then f a else 0

theorem hybridSupport_iff_remainder (removed : Finset ι) (i : ι) (hi : i∉removed)
    (core : α→Prop) (coprime : ι→α→Prop) (polynomial : ι→Prop) (a : α) :
    hybridSupport removed core coprime polynomial a ↔
      remainder removed i core coprime polynomial a ∧ coprime i a := by
  constructor
  · rintro ⟨hc,hall⟩
    exact ⟨⟨hc,fun q _=>hall q⟩,by simpa only [ite_eq_right hi] using hall i⟩
  · rintro ⟨⟨hc,hall⟩,hi'⟩
    refine ⟨hc,fun q=>?_⟩
    by_cases hq : q=i
    · subst q
      simpa only [ite_eq_right hi] using hi'
    · exact hall q hq

theorem hybridSupport_insert_iff (removed : Finset ι) (i : ι) (_hi : i∉removed)
    (core : α→Prop) (coprime : ι→α→Prop) (polynomial : ι→Prop) (a : α) :
    hybridSupport (insert i removed) core coprime polynomial a ↔
      remainder removed i core coprime polynomial a ∧ polynomial i := by
  constructor
  · rintro ⟨hc,hall⟩
    refine ⟨⟨hc,?_⟩,by simpa only [Finset.mem_insert_self,ite_true] using hall i⟩
    intro q hq
    simpa only [Finset.mem_insert,or_iff_right hq] using hall q
  · rintro ⟨⟨hc,hall⟩,hi'⟩
    refine ⟨hc,fun q=>?_⟩
    by_cases hq : q=i
    · subst q
      simpa only [Finset.mem_insert_self,ite_true] using hi'
    · simpa only [Finset.mem_insert,or_iff_right hq] using hall q hq

theorem norm_telescope_finset (F : Finset ι→ℂ) (error : ℝ)
    (hstep : ∀removed i,i∉removed → ‖F removed-F (insert i removed)‖≤error)
    (removed : Finset ι) : ‖F ∅-F removed‖≤(removed.card:ℝ)*error := by
  induction removed using Finset.induction_on with
  | empty => simp
  | @insert i removed hi ih =>
    calc
      _ = ‖(F ∅-F removed)+(F removed-F (insert i removed))‖ := by congr 1; ring
      _ ≤ ‖F ∅-F removed‖+‖F removed-F (insert i removed)‖ := norm_add_le _ _
      _ ≤ (removed.card:ℝ)*error+error := add_le_add ih (hstep removed i hi)
      _ = _ := by rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]; ring

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
