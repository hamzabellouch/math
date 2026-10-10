import Mathlib
import OAI.Computability.VertexCover.Machines.Naturals
import OAI.Computability.VertexCover.Machines.ListParam

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

noncomputable def Poly.listSingleton {α : Type} (ea : α → List Bool) :
    Poly ea (listBits ea) (fun a => [a]) := by
  exact (((Poly.identity ea).pair (Poly.const ea (listBits ea) [])).comp (Poly.listCons ea))

noncomputable def Poly.listFilter {α : Type} (ea : α → List Bool) (a₀ : α)
    {f : α → Bool} (cf : Poly ea boolBits f) :
    Poly (listBits ea) (listBits ea) (List.filter f) := by
  let c := cf.ite (Poly.listSingleton ea) (Poly.const ea (listBits ea) [])
  exact (Poly.listFlatMap ea ea a₀ a₀ c).congr (fun xs => by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      cases h : f a <;> simp [h,ih])

noncomputable def Poly.listFilterWith {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {f : α × β → Bool} (cf : Poly (prodBits ea eb) boolBits f) :
    Poly (prodBits ea (listBits eb)) (listBits eb)
      (fun p => p.2.filter (fun b => f (p.1,b))) := by
  let c := cf.ite ((Poly.snd ea eb).comp (Poly.listSingleton eb))
    (Poly.const (prodBits ea eb) (listBits eb) [])
  exact (((Poly.withParam ea eb a₀ b₀).comp
    (Poly.listFlatMap (prodBits ea eb) eb (a₀,b₀) b₀ c))).congr (fun p => by
    simp only [Function.comp_apply,List.flatMap_map]
    induction p.2 with
    | nil => rfl
    | cons b bs ih =>
      cases h : f (p.1,b) <;> simp [h,ih])

noncomputable def Poly.natLt : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1<p.2)) :=
  ((Poly.swap natBits natBits).comp Poly.natLE).comp (Poly.bool Bool.not) |>.congr
    (fun p => by
      by_cases h : p.1<p.2
      · have hn := Nat.not_le.mpr h
        simp [h,hn]
      · have hn := Nat.le_of_not_gt h
        simp [h,hn])

noncomputable def Poly.natEq : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => p.1 == p.2) := Poly.natBEq.congr (fun _ => rfl)

noncomputable def Poly.natPairEq : Poly (prodBits (prodBits natBits natBits) (prodBits natBits natBits))
    boolBits (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1 == p.2) := by
  let e := prodBits natBits natBits
  let a := Poly.fst e e
  let b := Poly.snd e e
  let cf := (((a.comp (Poly.fst natBits natBits)).pair
    (b.comp (Poly.fst natBits natBits))).comp Poly.natEq)
  let cs := (((a.comp (Poly.snd natBits natBits)).pair
    (b.comp (Poly.snd natBits natBits))).comp Poly.natEq)
  exact (cf.pair cs).comp (Poly.bool₂ (fun p => p.1 && p.2))

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
