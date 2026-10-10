import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.UnitIndexEnergy

namespace OAI

section
section
namespace ElementaryPositivity.SignedMultiplicity
variable {α : Type*} [DecidableEq α]

lemma pairwise_iff_count (even : α → Prop) (w : List α) :
    w.Pairwise (fun x y=>x=y → even x) ↔ ∀a,¬even a → w.count a≤1 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.pairwise_cons,ih]
    constructor
    · rintro ⟨hh,ht⟩ a ha
      by_cases hx : x=a
      · subst a
        have hn : x∉w := fun he=>ha (hh x he rfl)
        simp only [List.count_cons_self, List.count_eq_zero_of_not_mem hn]
        omega
      · simpa [List.count_cons,hx,eq_comm] using ht a ha
    · intro h
      constructor
      · intro y hy hxy
        subst y
        by_contra hn
        have hb:=h x hn
        have hp : 0<w.count x := List.count_pos_iff.mpr hy
        simp only [List.count_cons_self] at hb
        omega
      · intro a ha
        have hb:=h a ha
        have hl : w.count a≤(x::w).count a := List.count_le_count_cons
        omega

section Ordered
variable [LinearOrder α]

abbrev Word (even : α → Prop) :=
  {w : List α // w.Pairwise (·≤·) ∧ w.Pairwise (fun x y=>x=y → even x)}
abbrev Selection (even : α → Prop) := {m : Multiset α // ∀a,¬even a → m.count a≤1}

def wordSelectionEquiv (even : α → Prop) : Word even ≃ Selection even where
  toFun w:=⟨(w.val:Multiset α),by
    simpa only [Multiset.coe_count] using (pairwise_iff_count even w.val).mp w.property.2⟩
  invFun m:=⟨m.val.sort (·≤·),Multiset.pairwise_sort _ _,by
    apply (pairwise_iff_count even _).mpr
    intro a ha
    have hh:=m.property a ha
    simpa only [←Multiset.coe_count,Multiset.sort_eq] using hh⟩
  left_inv w:=by
    apply Subtype.ext
    change (w.val:Multiset α).sort (·≤·)=w.val
    exact List.Perm.eq_of_pairwise' (Multiset.pairwise_sort (w.val:Multiset α) (·≤·)) w.property.1
      (Quotient.exact (Multiset.sort_eq (w.val:Multiset α) (·≤·)))
  right_inv m:=Subtype.ext (Multiset.sort_eq m.val (·≤·))

lemma selection_sum {β : Type*} [AddCommMonoid β] (even : α → Prop) (f : α → β) (w : Word even) :
    (((wordSelectionEquiv even w).val).map f).sum=(w.val.map f).sum := rfl

abbrev CountSelection (even : α → Prop) := {f : α →₀ ℕ // ∀a,¬even a → f a≤1}

noncomputable def selectionCountEquiv (even : α → Prop) : Selection even ≃ CountSelection even :=
  Multiset.toFinsupp.toEquiv.subtypeEquiv (fun m=>by
    rfl)

noncomputable def wordCountEquiv (even : α → Prop) : Word even ≃ CountSelection even :=
  (wordSelectionEquiv even).trans (selectionCountEquiv even)
end Ordered
end ElementaryPositivity.SignedMultiplicity
end
namespace ElementaryPositivity.UnitSelections
noncomputable section
def unitEnergy (a n : ℕ) (k : ℤ) (f : UnitIndex a n) : ℤ :=
  (n:ℤ)*k-2*unitWeight a n f
end
end ElementaryPositivity.UnitSelections

section
namespace ElementaryPositivity.SignedMultiplicity
variable {A B : Type*}

lemma multiset_count_sum [DecidableEq A] {T : Type*} [AddCommMonoid T]
    (m : Multiset A) (e : A → T) :
    m.toFinsupp.sum (fun x n=>n • e x)=(m.map e).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    change (({x}:Multiset A)+m).toFinsupp.sum _=((({x}:Multiset A)+m).map e).sum
    rw [Multiset.toFinsupp_add]
    rw [Finsupp.sum_add_index' (h:=fun x n=>n • e x) (by simp)
      (by intro a b c; exact add_nsmul (e a) b c)]
    simp only [Multiset.toFinsupp_singleton,Multiset.map_add,Multiset.sum_add,
      Multiset.map_singleton,Multiset.sum_singleton,ih]
    rw [Finsupp.sum_single_index (h:=fun x n=>n • e x) (by simp),one_nsmul]

def countReindex (e : A ≃ B) (evenA : A → Prop) (evenB : B → Prop)
    (he : ∀a,evenA a ↔ evenB (e a)) : CountSelection evenA ≃ CountSelection evenB :=
  (Finsupp.equivCongrLeft e).subtypeEquiv (fun f=>by
    constructor
    · intro h b hb
      have ha : ¬evenA (e.symm b) := by simpa only [he,Equiv.apply_symm_apply] using hb
      exact h (e.symm b) ha
    · intro h a ha
      have hb : ¬evenB (e a):=by simpa only [he] using ha
      have hh:=h (e a) hb
      simpa only [Finsupp.equivCongrLeft_apply,Finsupp.equivMapDomain_apply,
        Equiv.symm_apply_apply] using hh)

lemma countReindex_sum (e : A ≃ B) (evenA : A → Prop) (evenB : B → Prop)
    (he : ∀a,evenA a ↔ evenB (e a)) (f : CountSelection evenA)
    {T : Type*} [AddCommMonoid T] (energy : B → T) :
    (countReindex e evenA evenB he f).val.sum (fun b n=>n • energy b)=
      f.val.sum (fun a n=>n • energy (e a)) :=
  Finsupp.sum_equivMapDomain e f.val (fun b n=>n • energy b)
end ElementaryPositivity.SignedMultiplicity
end
end

end OAI
