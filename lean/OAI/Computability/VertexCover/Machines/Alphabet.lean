import Mathlib
import OAI.Computability.VertexCover.Machines.AlphabetCorrect

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
open UniqueGames.Foundations.PCP

namespace TableMachine
 theorem materialize_source {α : Type} (Q : α → GraphTables.Table) (r : α × ℕ → Row)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) (a : α) :
    ((Q a).vertices,(List.range (Q a).darts).map (fun i => r (a,i))) = tableData (Q a) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [tableData]
  · intro i h₁ h₂
    simp only [tableData,List.getElem_map,List.getElem_range,Vector.getElem_toList]
    exact hr a ⟨i,by simpa using h₁⟩
noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α)
    (Q : α → GraphTables.Table) {r : α × ℕ → Row}
    (cn : Poly ea natBits (fun a => (Q a).vertices))
    (cm : Poly ea natBits (fun a => (Q a).darts))
    (cr : Poly (prodBits ea natBits) rowCode r)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) :
    Poly ea tableCode Q := by
  let rows := Poly.tabulate ea rowCode a₀ rowDefault cm cr
  exact (cn.pair rows).encodeCongr id (fun _ => rfl) (fun a => by
    exact congrArg dataCode (materialize_source Q r hr a))
end TableMachine

namespace AlphabetMachine
open AlphabetTable Enumeration
noncomputable def eventsPoly {q : ℕ} : Poly (GenericMachine.code (q := q)) natBits
    (fun T => eventCount T.darts q) :=
  ((GenericMachine.dartsPoly (q := q)).pair (Poly.const _ natBits (localCount q))).comp Poly.natMul
noncomputable def addressesPoly {q : ℕ} : Poly (GenericMachine.code (q := q)) natBits
    (fun T => addressCount T.vertices T.darts q) := by
  let v := ((GenericMachine.verticesPoly (q := q)).pair (Poly.const _ natBits (tapeCount q))).comp Poly.natMul
  let e := ((GenericMachine.dartsPoly (q := q)).pair (Poly.const _ natBits (pairTapeCount q))).comp Poly.natMul
  exact (v.pair e).comp Poly.natAdd
noncomputable def poly {q : ℕ} : Poly (GenericMachine.code (q := q)) TableMachine.tableCode Table.build := by
  let zero : GenericGraphTables.Table q := GenericGraphTables.ofGraph
    ({reverse := Equiv.refl (Fin 0),reverse_involutive := fun _ => rfl,
      tail := id,accepts := fun _ _ _ => true,reverse_accepts := fun _ _ _ => rfl} :
        ConstraintGraph (Fin 0) (Fin 0) (Fin q))
  exact TableMachine.materializePoly GenericMachine.code zero Table.build
    ((eventsPoly.pair addressesPoly).comp Poly.natAdd)
    ((eventsPoly.pair (Poly.const _ natBits 12)).comp Poly.natMul) rowPoly row_source
end AlphabetMachine
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
