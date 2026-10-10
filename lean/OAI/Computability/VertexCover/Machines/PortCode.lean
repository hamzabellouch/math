import Mathlib
import OAI.Computability.VertexCover.Machines.NatDiv
import OAI.Computability.VertexCover.Machines.TableBase

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

abbrev Data := ℕ × (List ℕ × List GraphTables.RelationTable)
def dataCode : Data → List Bool :=
  prodBits natBits (prodBits (listBits natBits) (listBits relationCode))
def erase {q : ℕ} (T : PortTables.Input q) : Data :=
  (T.1,(T.2.reverseIndex.toList.map Fin.val,T.2.relations.toList))
def code {q : ℕ} (T : PortTables.Input q) : List Bool := dataCode (erase T)

noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits Sigma.fst :=
  (Poly.fst natBits (prodBits (listBits natBits) (listBits relationCode))).encodeCongr
    erase (fun _ => rfl) (fun _ => rfl)
noncomputable def reverseListPoly {q : ℕ} :
    Poly (code (q := q)) (listBits natBits) (fun T => T.2.reverseIndex.toList.map Fin.val) :=
  ((Poly.snd natBits (prodBits (listBits natBits) (listBits relationCode))).comp
    (Poly.fst (listBits natBits) (listBits relationCode))).encodeCongr erase
      (fun _ => rfl) (fun _ => rfl)
noncomputable def relationListPoly {q : ℕ} :
    Poly (code (q := q)) (listBits relationCode) (fun T => T.2.relations.toList) :=
  ((Poly.snd natBits (prodBits (listBits natBits) (listBits relationCode))).comp
    (Poly.snd (listBits natBits) (listBits relationCode))).encodeCongr erase
      (fun _ => rfl) (fun _ => rfl)
noncomputable def reversePoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) natBits
    (fun p => (p.1.2.reverseIndex.toList.map Fin.val).getD p.2 0) :=
  (((Poly.snd code natBits).pair ((Poly.fst code natBits).comp reverseListPoly)).comp
    (Poly.listGetD natBits 0)).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])
noncomputable def relationPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) relationCode
    (fun p => p.1.2.relations.toList.getD p.2 relationDefault) :=
  (((Poly.snd code natBits).pair ((Poly.fst code natBits).comp relationListPoly)).comp
    (Poly.listGetD relationCode relationDefault)).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])

 theorem reverse_valid {q : ℕ} (T : PortTables.Input q) (i : Fin (T.1*q)) :
    (T.2.reverseIndex.toList.map Fin.val).getD i.val 0 = T.2.reverseIndex[i].val := by
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_map]
  rfl
 theorem relation_valid {q : ℕ} (T : PortTables.Input q) (i : Fin (T.1*q)) :
    T.2.relations.toList.getD i.val relationDefault = T.2.relations[i] := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  rfl

def graphRow (q : ℕ) (p : PortTables.Input q × ℕ) : TableMachine.Row :=
  ((p.2/q,(p.1.2.reverseIndex.toList.map Fin.val).getD p.2 0),
    p.1.2.relations.toList.getD p.2 relationDefault)

noncomputable def graphRowPoly (q : ℕ) :
    Poly (prodBits (code (q := q)) natBits) rowCode (graphRow q) := by
  let idx := Poly.snd (code (q := q)) natBits
  let t := (idx.pair (Poly.const _ natBits q)).comp Poly.natDiv
  exact (t.pair reversePoly).pair relationPoly

 theorem graphRow_source {q : ℕ} (T : PortTables.Input q) (i : Fin (T.1*q)) :
    graphRow q (T,i.val) = rowData (PortTables.graphTable T.2).rows[i] := by
  change graphRow q (T,i.val) = rowData (PortTables.flatRows T.2)[i.val]
  simp only [PortTables.flatRows,Vector.getElem_ofFn,rowData,graphRow,reverse_valid,
    relation_valid]
  rfl

def graphData {q : ℕ} (T : PortTables.Input q) : TableMachine.Data :=
  (T.1,(List.range (T.1*q)).map (fun i => graphRow q (T,i)))
 theorem graphData_source {q : ℕ} (T : PortTables.Input q) :
    graphData T = tableData (PortTables.graphTable T.2) := by
  apply Prod.ext
  · rfl
  · apply List.ext_getElem
    · simp [graphData,tableData,PortTables.graphTable]
    · intro i h₁ h₂
      simp only [graphData,tableData,List.getElem_map,List.getElem_range,Vector.getElem_toList]
      simpa only [Fin.getElem_fin] using graphRow_source T ⟨i,by simpa [graphData] using h₁⟩

noncomputable def graphDataPoly {q : ℕ} : Poly (code (q := q)) TableMachine.dataCode graphData := by
  let len := ((verticesPoly (q := q)).pair (Poly.const code natBits q)).comp Poly.natMul
  let empty : PortTables.Input q := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  exact verticesPoly.pair (Poly.tabulate code rowCode empty rowDefault len (graphRowPoly q))

noncomputable def graphPoly {q : ℕ} : Poly (code (q := q)) tableCode
    (fun T => PortTables.graphTable T.2) :=
  graphDataPoly.encodeCongr id (fun _ => rfl) (fun T => by
    change TableMachine.dataCode (graphData T) = TableMachine.dataCode _
    rw [graphData_source])

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
