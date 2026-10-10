import Mathlib

namespace OAI

section Inline_PCPOrdered

namespace MetricKMedian.PCP.Compiler
open scoped Classical

structure Ordered (A : Type) where
  entries : List A
  nodup : entries.Nodup
  all : ∀ a, a ∈ entries
namespace Ordered
variable {A B : Type} [DecidableEq A] [DecidableEq B]
def equiv (o : Ordered A) : A ≃ Fin o.entries.length :=
  (List.Nodup.getEquivOfForallMemList o.entries o.nodup o.all).symm
@[simp] lemma equiv_val (o : Ordered A) (a : A) : (o.equiv a).val=o.entries.idxOf a := rfl
lemma length_card [Fintype A] (o : Ordered A) : o.entries.length=Fintype.card A := by
  simpa only [Fintype.card_fin] using Fintype.card_congr o.equiv.symm
@[simp] lemma get_equiv (o : Ordered A) (a : A) : o.entries[(o.equiv a).val]=a :=
  o.equiv.symm_apply_apply a
def map (o : Ordered A) (e : A ≃ B) : Ordered B where
  entries := o.entries.map e
  nodup := o.nodup.map e.injective
  all b := List.mem_map.mpr ⟨e.symm b,o.all _,e.apply_symm_apply b⟩
def fin (n : ℕ) : Ordered (Fin n) where
  entries := List.finRange n
  nodup := List.nodup_finRange n
  all := List.mem_finRange
noncomputable def fixed (A : Type) [Fintype A] : Ordered A := (fin _).map (Fintype.equivFin A).symm

def filter (o : Ordered A) (p : A → Prop) [DecidablePred p] : Ordered {a // p a} where
  entries := o.entries.attach.filterMap (fun a => if h : p a.val then some ⟨a.val,h⟩ else none)
  nodup := by
    apply List.Nodup.filterMap _ o.nodup.attach
    intro a b c ha hb
    split_ifs at ha hb <;> simp_all
    exact Subtype.ext (congrArg (fun x : {a // p a} => x.val) (ha.trans hb.symm))
  all a := by
    apply List.mem_filterMap.mpr
    refine ⟨⟨a.val,o.all a.val⟩,List.mem_attach _ _,?_⟩
    simp only [dite_eq_left a.property]
end Ordered
end MetricKMedian.PCP.Compiler

end Inline_PCPOrdered

end OAI
