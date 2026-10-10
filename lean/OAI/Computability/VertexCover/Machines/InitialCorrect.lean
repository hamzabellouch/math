import Mathlib
import OAI.Computability.VertexCover.Machines.InitialTable

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

namespace VertexCover.Machine.InitialTable
open UniqueGames.Foundations
open PCP PCP.GraphTables FormulaParser TableMachine
open RawInitialTables

@[simp] theorem vertexOrder_variable (F : Target.Formula) (v : Fin F.variables) :
    (vertexOrder F (InitialGraph.variableVertex F v)).val = v.val := rfl
@[simp] theorem vertexOrder_clause (F : Target.Formula) (v : Fin F.clauses.length) :
    (vertexOrder F (InitialGraph.clauseVertex F v)).val = F.variables+v.val := rfl
@[simp] theorem vertexOrder_dummy (F : Target.Formula) :
    (vertexOrder F (InitialGraph.dummyVertex F)).val = F.variables+F.clauses.length := by
  change F.variables+F.clauses.length+0 = _
  omega

@[simp] theorem dartOrder_real (F : Target.Formula) (e : PCP.RandomEvent F) (b : Bool) :
    (dartOrder F (.inl (e,b))).val = (if b then 1 else 0)+2*((slotOrder e.2).val+3*e.1.val) := by
  cases b <;> rfl
@[simp] theorem dartOrder_dummy (F : Target.Formula) :
    (dartOrder F (InitialGraph.dummyDart F)).val = 6*F.clauses.length := by
  change F.clauses.length*3*2+0 = _
  omega

 theorem clause_lookup (F : Target.Formula) (j : Fin F.clauses.length) :
    (targetData F).2.getD j.val clauseDefault = targetClauseData (PCP.clauseAt F j) := by
  rw [List.getD_eq_getElem _ _ (by simp [targetData])]
  simp only [targetData,List.getElem_map,PCP.clauseAt]

 theorem lit_target (F : Target.Formula) (e : PCP.RandomEvent F) :
    (lit (targetClauseData (PCP.clauseAt F e.1)) (slotOrder e.2)).2 =
      (PCP.nameAt (PCP.clauseAt F e.1) e.2).val := by
  rcases e with ⟨j,s⟩
  cases s <;> rfl

 theorem relation_target (F : Target.Formula) (e : PCP.RandomEvent F) (b : Bool) :
    relation (signs (targetClauseData (PCP.clauseAt F e.1)),(slotOrder e.2,b)) =
      relationOf (fun a c => (raw64 F).accepts (.inl (e,b))
        (labelOrder.symm a) (labelOrder.symm c)) := by
  apply congrArg relationOf
  funext a c
  rcases e with ⟨j,s⟩
  cases s <;> cases b <;> rfl

 theorem real_row (F : Target.Formula) (e : PCP.RandomEvent F) (b : Bool) :
    row (targetData F,(dartOrder F (.inl (e,b))).val) =
      (((vertexOrder F ((raw64 F).tail (.inl (e,b)))).val,
        (dartOrder F ((raw64 F).reverse (.inl (e,b)))).val),
        relationOf (fun a c => (raw64 F).accepts (.inl (e,b))
          (labelOrder.symm a) (labelOrder.symm c))) := by
  let idx := (dartOrder F (.inl (e,b))).val
  have hs : (slotOrder e.2).val < 3 := (slotOrder e.2).isLt
  have hi : idx < 6*F.clauses.length := by
    dsimp [idx]; rw [dartOrder_real]
    have hj := e.1.isLt
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have hd : idx/6=e.1.val := by
    dsimp [idx]; rw [dartOrder_real]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have hp : (⟨(idx/2)%3,Nat.mod_lt _ (by decide)⟩ : Fin 3)=slotOrder e.2 := by
    apply Fin.ext
    dsimp [idx]; rw [dartOrder_real]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have hb : decide (idx%2=1)=b := by
    simp only [idx,dartOrder_real]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,decide_eq_false_iff_not,decide_eq_true_eq] <;> omega
  change row (targetData F,idx) = _
  dsimp only [row]
  rw [show (targetData F).2.length=F.clauses.length by simp [targetData],ite_eq_left hi,hd,hp,hb,
    clause_lookup,lit_target,relation_target]
  apply Prod.ext
  · apply Prod.ext
    · cases b <;> rfl
    · cases b with
      | false =>
        change idx+1 = (dartOrder F (.inl (e,true))).val
        simp only [idx,dartOrder_real,Bool.false_eq_true,↓reduceIte]
        omega
      | true =>
        change idx-1 = (dartOrder F (.inl (e,false))).val
        simp only [idx,dartOrder_real,Bool.false_eq_true,↓reduceIte]
        omega
  · rfl

 theorem dummy_row (F : Target.Formula) :
    row (targetData F,(dartOrder F (InitialGraph.dummyDart F)).val) =
      (((vertexOrder F ((raw64 F).tail (InitialGraph.dummyDart F))).val,
        (dartOrder F ((raw64 F).reverse (InitialGraph.dummyDart F))).val),
        relationOf (fun a c => (raw64 F).accepts (InitialGraph.dummyDart F)
          (labelOrder.symm a) (labelOrder.symm c))) := by
  rw [dartOrder_dummy]
  simp only [row,targetData,List.length_map,lt_self_iff_false,↓reduceIte]
  change _ = ((F.variables+F.clauses.length+0,F.clauses.length*3*2+0),_)
  congr 2; omega

 theorem row_target (F : Target.Formula) (i : Fin (table F).darts) :
    row (targetData F,i.val) = rowData (table F).rows[i] := by
  obtain ⟨d,rfl⟩ := (dartOrder F).surjective i
  have he : rowData (table F).rows[dartOrder F d] =
      (((vertexOrder F ((raw64 F).tail d)).val,(dartOrder F ((raw64 F).reverse d)).val),
        relationOf (fun a c => (raw64 F).accepts d (labelOrder.symm a) (labelOrder.symm c))) := by
    have getrow {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m) Label) (j : Fin m) :
        rowData (graphRows G)[j] =
          ((G.tail j |>.val,G.reverse j |>.val),relationOf (G.accepts j)) := by
      change rowData (graphRows G)[j.val] = _
      simp only [graphRows,Vector.getElem_ofFn,rowData]
    change rowData (graphRows (enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder))[dartOrder F d] = _
    rw [getrow]
    simp only [enumeratedGraph,Equiv.trans_apply,Equiv.symm_apply_apply]
  apply Eq.trans _ he.symm
  cases d with
  | inl eb => exact real_row F eb.1 eb.2
  | inr u => cases u; exact dummy_row F

 theorem output_target (F : Target.Formula) : output (targetData F)=tableData (table F) := by
  apply Prod.ext
  · simp only [output,targetData,tableData,table_vertices,List.length_map]
  · apply List.ext_getElem
    · simp only [output,tableData,List.length_map,List.length_range,targetData]
      exact (table_darts F).symm.trans (Vector.length_toList (xs := (table F).rows)).symm
    · intro i h₁ h₂
      simp only [output,List.getElem_map,List.getElem_range,tableData] at *
      simpa only [Fin.getElem_fin,Vector.getElem_toList] using
        row_target F ⟨i,by simpa [output,targetData,table_darts] using h₁⟩

noncomputable def initialPoly : Poly targetCode tableCode table :=
  outputPoly.encodeCongr targetData (fun _ => rfl) (fun F => by
    change TableMachine.dataCode (output (targetData F)) = TableMachine.dataCode (tableData (table F))
    rw [output_target])

end VertexCover.Machine.InitialTable
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
