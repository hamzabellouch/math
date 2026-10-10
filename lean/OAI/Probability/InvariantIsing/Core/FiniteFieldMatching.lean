import OAI.Probability.InvariantIsing.Fields.SpinGroupSlice
import Mathlib.Logic.Equiv.Fintype

namespace OAI

/-! Match as many sites of each field label as both finite populations contain. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

def fieldLabelInjection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g : Fin N → A) (s : A → ℕ) (hs : ∀ a, s a ≤ spinGroupSize g a) :
    (Σ a, Fin (s a)) ↪ Fin N where
  toFun x := ((Fintype.equivFin {i : Fin N // g i=x.1}).symm
    (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs x.1) x.2)).val
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ he
    have ha : g ((Fintype.equivFin {i : Fin N // g i=a}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs a) i)).val=a :=
      ((Fintype.equivFin {i : Fin N // g i=a}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs a) i)).property
    have hb : g ((Fintype.equivFin {i : Fin N // g i=b}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs b) j)).val=b :=
      ((Fintype.equivFin {i : Fin N // g i=b}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs b) j)).property
    have hab : a=b := ha.symm.trans ((congrArg g he).trans hb)
    subst b
    have hh := (Fintype.equivFin {i : Fin N // g i=a}).symm.injective (Subtype.ext he)
    have hij : i=j := by
      apply Fin.ext
      exact congrArg (fun z : Fin (Fintype.card {i : Fin N // g i=a}) => z.val) hh
    subst j
    rfl

lemma fieldLabelInjection_label {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g : Fin N → A) (s : A → ℕ) (hs : ∀ a, s a ≤ spinGroupSize g a)
    (x : Σ a, Fin (s a)) : g (fieldLabelInjection g s hs x)=x.1 :=
  ((Fintype.equivFin {i : Fin N // g i=x.1}).symm
    (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs x.1) x.2)).property

theorem exists_field_label_matching {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g h : Fin N → A) : ∃ p : Equiv.Perm (Fin N),
      (Finset.univ.filter (fun i => g i=h (p i))).card ≥
        ∑ a, min (spinGroupSize g a) (spinGroupSize h a) := by
  let s := fun a => min (spinGroupSize g a) (spinGroupSize h a)
  let f := fieldLabelInjection g s (fun a => min_le_left _ _)
  let k := fieldLabelInjection h s (fun a => min_le_right _ _)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f k f.injective k.injective
  refine ⟨p,?_⟩
  have hsub : Finset.univ.image f ⊆ Finset.univ.filter (fun i => g i=h (p i)) := by
    intro i hi
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hp]
    exact (fieldLabelInjection_label g s _ x).trans (fieldLabelInjection_label h s _ x).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ f.injective] at hc
  simpa only [Finset.card_univ, Fintype.card_sigma, Fintype.card_fin, s] using hc

end InvariantIsing

end

end OAI
