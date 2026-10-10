import Mathlib
import OAI.Computability.VertexCover.Machines.Primitives

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

theorem prodBits_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Function.Injective ea) (hb : Function.Injective eb) :
    Function.Injective (prodBits ea eb) := by
  intro a b h
  apply Prod.ext
  · apply ha
    have hh := congrArg (Stream.output (Project.trans true false) (fun _ => []) 0) h
    simpa only [prodBits,Project.framed,Bool.false_eq_true,↓reduceIte,List.append_nil] using hh
  · apply hb
    have hh := congrArg (Stream.output (Project.trans false true) (fun _ => []) 0) h
    simpa only [prodBits,Project.framed,Bool.false_eq_true,↓reduceIte,List.nil_append] using hh

theorem boolBits_injective : Function.Injective boolBits := by
  intro a b h
  exact List.singleton_injective h

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
