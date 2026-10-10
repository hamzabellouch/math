import Mathlib
import OAI.Computability.VertexCover.PCP.AlphabetTableTable
import OAI.Computability.VertexCover.Machines.ListNat
import OAI.Computability.VertexCover.Machines.ListParam
import OAI.Computability.VertexCover.Machines.Option

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
open UniqueGames.Foundations

noncomputable def Poly.tabulate {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {n : α → ℕ} {f : α × ℕ → β}
    (cn : Poly ea natBits n) (cf : Poly (prodBits ea natBits) eb f) :
    Poly ea (listBits eb) (fun a => (List.range (n a)).map (fun i => f (a,i))) :=
  (((Poly.identity ea).pair (cn.comp Poly.range)).comp
    (Poly.listMapWith ea natBits eb a₀ 0 b₀ cf)).congr (fun _ => rfl)

namespace TableMachine
open PCP.GraphTables

abbrev Row := (ℕ × ℕ) × RelationTable
abbrev Data := ℕ × List Row

def relationCode (r : RelationTable) : List Bool := r.toList
def rowCode : Row → List Bool := prodBits (prodBits natBits natBits) relationCode
def dataCode : Data → List Bool := prodBits natBits (listBits rowCode)
def rowData {n m : ℕ} (r : DartRow n m) : Row := ((r.tail.val,r.reverseIndex.val),r.relation)
def tableData (T : Table) : Data := (T.vertices,T.rows.toList.map rowData)
def tableCode (T : Table) : List Bool := dataCode (tableData T)

def relationDefault : RelationTable := Vector.replicate 4096 false
def rowDefault : Row := ((0,0),relationDefault)

@[simp] theorem relationCode_length (r : RelationTable) : (relationCode r).length = 4096 := by
  simp [relationCode]

noncomputable def verticesPoly : Poly tableCode natBits Table.vertices :=
  (Poly.fst natBits (listBits rowCode)).encodeCongr tableData (fun _ => rfl) (fun _ => rfl)

noncomputable def rowsPoly : Poly tableCode (listBits rowCode) (fun T => T.rows.toList.map rowData) :=
  (Poly.snd natBits (listBits rowCode)).encodeCongr tableData (fun _ => rfl) (fun _ => rfl)

noncomputable def dartsPoly : Poly tableCode natBits Table.darts :=
  (rowsPoly.comp (Poly.listLength rowCode rowDefault)).congr (fun T => by simp)

noncomputable def lookupPoly : Poly (prodBits tableCode natBits) rowCode
    (fun p : Table × ℕ => (tableData p.1).2.getD p.2 rowDefault) := by
  let rows := (Poly.fst tableCode natBits).comp rowsPoly
  let idx := Poly.snd tableCode natBits
  exact ((idx.pair rows).comp (Poly.listGetD rowCode rowDefault)).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD]
    rfl)

noncomputable def tailPoly : Poly (prodBits tableCode natBits) natBits
    (fun p : Table × ℕ => ((tableData p.1).2.getD p.2 rowDefault).1.1) :=
  lookupPoly.comp ((Poly.fst (prodBits natBits natBits) relationCode).comp (Poly.fst natBits natBits))

noncomputable def reversePoly : Poly (prodBits tableCode natBits) natBits
    (fun p : Table × ℕ => ((tableData p.1).2.getD p.2 rowDefault).1.2) :=
  lookupPoly.comp ((Poly.fst (prodBits natBits natBits) relationCode).comp (Poly.snd natBits natBits))

noncomputable def relationPoly : Poly (prodBits tableCode natBits) relationCode
    (fun p : Table × ℕ => ((tableData p.1).2.getD p.2 rowDefault).2) :=
  lookupPoly.comp (Poly.snd (prodBits natBits natBits) relationCode)

@[simp] theorem lookup_valid (T : Table) (i : Fin T.darts) :
    (tableData T).2.getD i.val rowDefault = rowData T.rows[i] := by
  simp only [tableData,List.getD_eq_getElem?_getD,List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp)]
  rfl

end TableMachine
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
