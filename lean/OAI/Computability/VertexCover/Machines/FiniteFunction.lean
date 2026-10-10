import Mathlib
import OAI.Computability.VertexCover.Machines.Codec
import OAI.Computability.VertexCover.Machines.LCData

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

noncomputable def Poly.finFunction {α β : Type} [Fintype β]
    (ea : α → List Bool) : (n : ℕ) → (f : α → Fin n → β) →
    (∀ i, Poly ea (finiteCode β) (fun a => f a i)) →
    Poly ea (finiteCode (Fin n → β)) f
  | 0,f,_ => (Poly.const ea (finiteCode (Fin 0 → β)) (fun i => Fin.elim0 i)).congr
    (fun a => by funext i; exact Fin.elim0 i)
  | n+1,f,cf =>
    (((cf 0).pair (Poly.finFunction ea n (fun a i => f a i.succ) (fun i => cf i.succ))).comp
      (Poly.finite _ _ (prodBits_injective (finiteCode_injective β) (finiteCode_injective (Fin n → β)))
        (fun p : β × (Fin n → β) => Fin.cons p.1 p.2))).congr
          (fun a => by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl)

noncomputable def Poly.finiteFunction {α β ι : Type} [Fintype β] [Fintype ι] [DecidableEq ι]
    (ea : α → List Bool) (f : α → ι → β)
    (cf : ∀ i, Poly ea (finiteCode β) (fun a => f a i)) :
    Poly ea (finiteCode (ι → β)) f := by
  let E := Fintype.equivFin ι
  exact ((Poly.finFunction ea (Fintype.card ι) (fun a i => f a (E.symm i))
    (fun i => cf (E.symm i))).comp
      (Poly.finite _ _ (finiteCode_injective _) (fun g : Fin (Fintype.card ι) → β => fun i => g (E i)))).congr
        (fun a => by funext i; exact congrArg (f a) (E.symm_apply_apply i))

noncomputable def Poly.finiteRecode {α : Type} [Fintype α] (ea : α → List Bool)
    (ha : Function.Injective ea) : Poly ea (finiteCode α) id :=
  Poly.finite ea (finiteCode α) ha id

noncomputable def Poly.fixedSum {α ι : Type} (ea : α → List Bool)
    (f : α → ι → ℕ) (cf : ∀ i, Poly ea natBits (fun a => f a i)) :
    (xs : List ι) → Poly ea natBits (fun a => (xs.map (f a)).sum)
  | [] => (Poly.const ea natBits 0).congr (fun _ => rfl)
  | i::xs => (((cf i).pair (Poly.fixedSum ea f cf xs)).comp Poly.natAdd).congr
    (fun a => by simp only [Function.comp_apply,List.map_cons,List.sum_cons])

noncomputable def Poly.finiteSum {α ι : Type} [Fintype ι] (ea : α → List Bool)
    (f : α → ι → ℕ) (cf : ∀ i, Poly ea natBits (fun a => f a i)) :
    Poly ea natBits (fun a => ∑ i, f a i) := by
  classical
  exact (Poly.fixedSum ea f cf Finset.univ.toList).congr (fun a => by simp)
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
