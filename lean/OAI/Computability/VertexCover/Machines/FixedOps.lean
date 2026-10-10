import Mathlib
import OAI.Computability.VertexCover.Machines.Naturals

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.Machine

noncomputable def Poly.fixedList {α ι β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → ι → β) (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    (xs : List ι) → Poly ea (listBits eb) (fun a => xs.map (f a))
  | [] => Poly.const ea (listBits eb) []
  | i::xs => ((cf i).pair (Poly.fixedList ea eb f cf xs)).comp (Poly.listCons eb)

noncomputable def Poly.fixedAll {α ι : Type} (ea : α → List Bool) (f : α → ι → Bool)
    (cf : ∀ i, Poly ea boolBits (fun a => f a i)) :
    (xs : List ι) → Poly ea boolBits (fun a => xs.all (f a))
  | [] => Poly.const ea boolBits true
  | i::xs => (((cf i).pair (Poly.fixedAll ea f cf xs)).comp (Poly.bool₂ (fun x => x.1 && x.2))).congr
     (fun _ => by simp only [Function.comp_apply,List.all_cons])

noncomputable def Poly.finiteAll {α ι : Type} [Fintype ι] (ea : α → List Bool)
    (f : α → ι → Bool) (cf : ∀ i, Poly ea boolBits (fun a => f a i)) :
    Poly ea boolBits (fun a => decide (∀ i, f a i = true)) := by
  classical
  exact (Poly.fixedAll ea f cf Finset.univ.toList).congr (fun a => by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,Finset.mem_toList,Finset.mem_univ,forall_const,decide_eq_true_iff])

noncomputable def fixedSelect {α ι β : Type} [DecidableEq ι]
    (f : α → ι → β) (i₀ : ι) : List ι → α × ι → β
  | [], x => f x.1 i₀
  | i::xs, x => if x.2=i then f x.1 i else fixedSelect f i₀ xs x

theorem fixedSelect_mem {α ι β : Type} [DecidableEq ι]
    (f : α → ι → β) (i₀ : ι) (a : α) :
    ∀ (xs : List ι) (i : ι), i ∈ xs → fixedSelect f i₀ xs (a,i) = f a i := by
  intro xs
  induction xs with
  | nil => simp
  | cons j xs ih =>
    intro i hi
    by_cases h : i=j
    · subst i; simp [fixedSelect]
    · rw [fixedSelect,ite_eq_right h]
      exact ih i ((List.mem_cons.mp hi).resolve_left h)

noncomputable def Poly.fixedSelect {α ι β : Type} [Fintype ι] [DecidableEq ι]
    (ea : α → List Bool) (ei : ι → List Bool) (eb : β → List Bool) (hi : Function.Injective ei)
    (f : α → ι → β) (i₀ : ι) (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    (xs : List ι) → Poly (prodBits ea ei) eb (fixedSelect f i₀ xs)
  | [] => (Poly.fst ea ei).comp (cf i₀)
  | i::xs => (((Poly.snd ea ei).comp (Poly.finite ei boolBits hi (fun j => decide (j=i)))).ite
    ((Poly.fst ea ei).comp (cf i)) (Poly.fixedSelect ea ei eb hi f i₀ cf xs)).congr (fun _ => by
      simp only [Function.comp_apply,VertexCover.Machine.fixedSelect,decide_eq_true_eq])

noncomputable def Poly.finiteBranch {α ι β : Type} [Fintype ι] [Nonempty ι]
    (ea : α → List Bool) (ei : ι → List Bool) (eb : β → List Bool) (hi : Function.Injective ei)
    (f : α → ι → β) (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    Poly (prodBits ea ei) eb (fun x => f x.1 x.2) := by
  classical
  let i₀ := Classical.choice (inferInstance : Nonempty ι)
  exact (Poly.fixedSelect ea ei eb hi f i₀ cf Finset.univ.toList).congr
    (fun x => fixedSelect_mem f i₀ x.1 _ x.2 (by simp))

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
