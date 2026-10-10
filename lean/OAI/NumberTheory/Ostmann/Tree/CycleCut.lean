import OAI.NumberTheory.Ostmann.Tree.DensityCut

namespace OAI

namespace Ostmann.Tree.Density.Cut
open scoped BigOperators

def label : {d k : ℕ} → Cut d k → Leaves d → Leaves k
  | _,_,.stop _,_ => fun i => Fin.elim0 i
  | _,_,.split L R,v => if v 0 then Fin.cons true (label R (Fin.tail v))
      else Fin.cons false (label L (Fin.tail v))

@[simp] theorem label_cons_false {d k : ℕ} (L R : Cut d k) (v : Leaves d) :
    label (.split L R) (Fin.cons false v)=Fin.cons false (label L v) := by simp [label]
@[simp] theorem label_cons_true {d k : ℕ} (L R : Cut d k) (v : Leaves d) :
    label (.split L R) (Fin.cons true v)=Fin.cons true (label R v) := by simp [label]

theorem label_surjective {d k : ℕ} (C : Cut d k) : Function.Surjective (label C) := by
  induction C with
  | stop d =>
    intro v
    exact ⟨fun _ => false,Subsingleton.elim _ _⟩
  | @split d k L R ihl ihr =>
    intro v
    obtain ⟨⟨b,w⟩,rfl⟩ := (Density.pathEquiv k).surjective v
    cases b with
    | false =>
      obtain ⟨e,he⟩ := ihl w
      refine ⟨Fin.cons false e, ?_⟩
      change label (.split L R) (Fin.cons false e)=Fin.cons false w
      rw [label_cons_false,he]
    | true =>
      obtain ⟨e,he⟩ := ihr w
      refine ⟨Fin.cons true e, ?_⟩
      change label (.split L R) (Fin.cons true e)=Fin.cons true w
      rw [label_cons_true,he]

theorem project_eq_label_product {F : Type*} [Field F] {d k : ℕ} (C : Cut d k)
    (M : Leaves d → Fˣ) (v : Leaves k) :
    project C M v = ∏ e with label C e=v, M e := by
  classical
  induction C with
  | stop d =>
    have hv : ∀e : Leaves d,label (.stop d) e=v := fun _ => Subsingleton.elim _ _
    simp [project,Parameters.leafProduct,hv]
  | @split d k L R ihl ihr =>
    obtain ⟨⟨b,w⟩,rfl⟩ := (Density.pathEquiv k).surjective v
    change project (.split L R) M (Fin.cons b w) =
      ∏ e with label (.split L R) e=Fin.cons b w, M e
    cases b <;>
      simp only [project,Density.join,Fin.cons_zero,Fin.tail_cons,
        Bool.false_eq_true,↓reduceIte] <;>
      rw [Finset.prod_filter,Density.prod_split] <;>
      simp only [Density.left,Density.right,label_cons_false,label_cons_true,
        Fin.cons_inj, Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
        ↓reduceIte,Finset.prod_const_one,mul_one,one_mul] <;>
      rw [← Finset.prod_filter]
    · exact ihl _ _
    · exact ihr _ _

end Ostmann.Tree.Density.Cut

end OAI
