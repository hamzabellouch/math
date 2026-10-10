import Mathlib
import OAI.Computability.MinUncut.Search.FiniteEnumeration

namespace OAI

section
namespace MinUncut.Enumeration
variable {A B C : Type}
def mapEquiv (E : Enumeration A) (e : A ≃ B) : Enumeration B where
  values := E.values.map e
  nodup := E.nodup.map e.injective
  complete b := List.mem_map.mpr ⟨e.symm b,E.complete _,e.apply_symm_apply b⟩
def bind (E : Enumeration A) {B : A → Type} (F : ∀a,Enumeration (B a)) : Enumeration (Σa,B a) where
  values := E.values.flatMap (fun a=>(F a).values.map (Sigma.mk a))
  nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro a _
      exact (F a).nodup.map (by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2)
    · apply E.nodup.pairwise_of_forall_ne
      intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hx hy
      obtain ⟨u,_,rfl⟩:=List.mem_map.mp hx
      obtain ⟨v,_,he⟩:=List.mem_map.mp hy
      exact hab (Sigma.mk.inj he).1.symm
  complete x := by
    rcases x with ⟨a,b⟩
    exact List.mem_flatMap.mpr ⟨a,E.complete a,List.mem_map.mpr ⟨b,(F a).complete b,rfl⟩⟩
def filterSubtype (E : Enumeration A) (p : A → Prop) [DecidablePred p] : Enumeration {a // p a} where
  values := (E.values.filter p).attach.map (fun a=>(⟨a.val,by simpa only [decide_eq_true_eq] using (List.mem_filter.mp a.property).2⟩ : {a // p a}))
  nodup := (List.nodup_attach.mpr (E.nodup.filter _)).map (by intro a b h; apply Subtype.ext; exact congrArg (fun x : {a // p a}=>x.val) h)
  complete a := by
    apply List.mem_map.mpr
    exact ⟨⟨a.val,List.mem_filter.mpr ⟨E.complete a.val,by simpa only [decide_eq_true_eq] using a.property⟩⟩,List.mem_attach _ _,rfl⟩
lemma filterSubtype_flatMap (E : Enumeration A) (p : A → Prop) [DecidablePred p]
    (f : A → List B) :
    (E.filterSubtype p).values.flatMap (fun a=>f a.val)=
      E.values.flatMap (fun a=>if p a then f a else []) := by
  unfold filterSubtype
  simp only [List.flatMap_map]
  rw [show List.flatMap (fun a : {a // a∈E.values.filter p}=>f a.val) (E.values.filter p).attach =
      (E.values.filter p).flatMap f by
    rw [←List.flatMap_map (g:=f) (f:=Subtype.val),List.attach_map_subtype_val]]
  generalize E.values = xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons,List.flatMap_cons]
    by_cases hx:p x <;> simp [hx,ih]
end MinUncut.Enumeration

end

end OAI
