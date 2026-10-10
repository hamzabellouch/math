import Mathlib
import OAI.Computability.VertexCover.Machines.FiniteMemory

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

def optionBits {α : Type} (ea : α → List Bool) : Option α → List Bool
  | none => [false]
  | some a => true::ea a

noncomputable def Poly.some {α : Type} (ea : α → List Bool) :
    Poly ea (optionBits ea) Option.some :=
  (Poly.cons true).encodeCongr ea (fun _ => rfl) (fun _ => rfl)

noncomputable def Poly.isSome {α : Type} (ea : α → List Bool) :
    Poly (optionBits ea) boolBits Option.isSome :=
  (Poly.headD false).encodeCongr (optionBits ea) (fun _ => rfl) (fun a => by cases a <;> rfl)

noncomputable def Poly.getD {α : Type} (ea : α → List Bool) (a₀ : α) :
    Poly (optionBits ea) ea (fun o => o.getD a₀) := by
  let test := Poly.headD false
  let c := test.ite Poly.tail (Poly.const id id (ea a₀))
  exact c.encodeCongr (optionBits ea) (fun _ => rfl) (fun a => by cases a <;> rfl)

noncomputable def Poly.optionMap {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) {f : α → β} (cf : Poly ea eb f) :
    Poly (optionBits ea) (optionBits eb) (Option.map f) :=
  ((Poly.isSome ea).ite (((Poly.getD ea a₀).comp cf).comp (Poly.some eb))
    (Poly.const (optionBits ea) (optionBits eb) none)).congr (fun a => by cases a <;> rfl)

noncomputable def Poly.optionBind {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) {f : α → Option β} (cf : Poly ea (optionBits eb) f) :
    Poly (optionBits ea) (optionBits eb) (fun o => o.bind f) :=
  ((Poly.isSome ea).ite ((Poly.getD ea a₀).comp cf)
    (Poly.const (optionBits ea) (optionBits eb) none)).congr (fun a => by cases a <;> rfl)

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
