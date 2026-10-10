import Mathlib
import OAI.Computability.VertexCover.Machines.PortCode

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

namespace VertexCover.Machine.PortMachine
open UniqueGames.Foundations.PCP
open TableMachine

 theorem materialize_source {α : Type} {q : ℕ} (Q : α → PortTables.Input q)
    (r : α × ℕ → ℕ) (s : α × ℕ → GraphTables.RelationTable)
    (hr : ∀ a (i : Fin ((Q a).1*q)), r (a,i.val) = (Q a).2.reverseIndex[i].val)
    (hs : ∀ a (i : Fin ((Q a).1*q)), s (a,i.val) = (Q a).2.relations[i]) (a : α) :
    ((Q a).1,((List.range ((Q a).1*q)).map (fun i => r (a,i)),
      (List.range ((Q a).1*q)).map (fun i => s (a,i)))) = erase (Q a) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply List.ext_getElem
      · simp [erase]
      · intro i h₁ h₂
        simp only [erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact hr a ⟨i,by simpa using h₁⟩
    · apply List.ext_getElem
      · simp [erase]
      · intro i h₁ h₂
        simp only [erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
        exact hs a ⟨i,by simpa using h₁⟩
noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α) {q : ℕ}
    (Q : α → PortTables.Input q) {r : α × ℕ → ℕ} {s : α × ℕ → GraphTables.RelationTable}
    (cn : Poly ea natBits (fun a => (Q a).1))
    (cr : Poly (prodBits ea natBits) natBits r)
    (cs : Poly (prodBits ea natBits) relationCode s)
    (hr : ∀ a (i : Fin ((Q a).1*q)), r (a,i.val) = (Q a).2.reverseIndex[i].val)
    (hs : ∀ a (i : Fin ((Q a).1*q)), s (a,i.val) = (Q a).2.relations[i]) :
    Poly ea code Q := by
  let len := (cn.pair (Poly.const ea natBits q)).comp Poly.natMul
  let rc := Poly.tabulate ea natBits a₀ 0 len cr
  let sc := Poly.tabulate ea relationCode a₀ relationDefault len cs
  let c := cn.pair (rc.pair sc)
  exact c.encodeCongr id (fun _ => rfl) (fun a => by
    change dataCode _ = dataCode _
    exact congrArg dataCode (materialize_source Q r s hr hs a))

end VertexCover.Machine.PortMachine
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
