import Mathlib

namespace OAI

namespace Ostmann.Arithmetic.OccurrencePermutation

theorem exists_occurrence_equiv {A : Type*} {xs ys : List A} (h : xs.Perm ys) :
    ∃e : Fin xs.length ≃ Fin ys.length, ∀i,ys.get (e i)=xs.get i := by
  classical
  induction h with
  | nil => exact ⟨Equiv.refl _,fun i => Fin.elim0 i⟩
  | @cons a xs ys h ih =>
    obtain ⟨e,he⟩ := ih
    let e' := ((finSuccEquiv xs.length).trans (Equiv.optionCongr e)).trans
      (finSuccEquiv ys.length).symm
    refine ⟨e',?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e']
    · simpa [e'] using he j
  | swap a b xs =>
    refine ⟨Equiv.swap 0 1,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · have h0 : k.succ.succ ≠ (0 : Fin (xs.length+2)) := Fin.succ_ne_zero _
        have h1 : k.succ.succ ≠ (1 : Fin (xs.length+2)) := by
          intro he
          have hv := congrArg Fin.val he
          norm_num [Fin.val_succ,Fin.val_one] at hv
        simp [Equiv.swap_apply_def,h0,h1]
  | trans h1 h2 ih1 ih2 =>
    obtain ⟨e,he⟩ := ih1
    obtain ⟨f,hf⟩ := ih2
    exact ⟨e.trans f,fun i => (hf (e i)).trans (he i)⟩

noncomputable def indexEquiv {A : Type*} {xs ys : List A} (h : xs.Perm ys) :
    Fin xs.length ≃ Fin ys.length := Classical.choose (exists_occurrence_equiv h)

theorem get_indexEquiv {A : Type*} {xs ys : List A} (h : xs.Perm ys)
    (i : Fin xs.length) : ys.get (indexEquiv h i)=xs.get i :=
  Classical.choose_spec (exists_occurrence_equiv h) i

end Ostmann.Arithmetic.OccurrencePermutation

end OAI
