import Mathlib
import OAI.Computability.VertexCover.Machines.Iteration
import OAI.Computability.VertexCover.Machines.FinalCNF

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

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.GraphTables PCP.VerifierToCNF FormulaParser TableMachine

 theorem rename_old (T : Table) (e : Fin T.darts) (r : RelationTable) (i : Fin 12) :
    rename (T,e.val) (oldIndex (localVerifier r) ((localVerifier r).query (0 : Fin 1) i)).val =
      (oldIndex (Complexity.FinalCNFPattern.tableVerifier T)
        ((Complexity.FinalCNFPattern.tableVerifier T).query e i)).val := by
  simp only [oldIndex_value]
  have hi : ((localVerifier r).query (0 : Fin 1) i).val = i.val := rfl
  rw [hi,rename,dite_eq_left i.isLt]
  exact queryName_correct T e i

 theorem rename_fresh (T : Table) (e : Fin T.darts) (r : RelationTable)
    (p : PatternIndex 12) (j : Fin (12-3)) :
    rename (T,e.val) (freshIndex (localVerifier r) (0 : Fin 1) p j).val =
      (freshIndex (Complexity.FinalCNFPattern.tableVerifier T) e p j).val := by
  have hleft := freshIndex_value (localVerifier r) (0 : Fin 1) p j
  rw [hleft, freshIndex_value]
  change rename (T,e.val) (12+((0*(patterns 12).length+p.val)*9+j.val)) =
    T.vertices*6+((e.val*(patterns 12).length+p.val)*9+j.val)
  have h : ¬12+((0*(patterns 12).length+p.val)*9+j.val)<12 := by omega
  rw [rename,dite_eq_right h]
  simp only [Nat.zero_mul,Nat.zero_add,Nat.add_sub_cancel_left]
  ring

 theorem event_correct (T : Table) (e : Fin T.darts) :
    eventData (T,e.val) =
      (eventBlock (Complexity.FinalCNFPattern.tableVerifier T) (by decide) e).map targetClauseData := by
  unfold eventData
  rw [lookup_valid]
  simp only [skeleton,List.map_map,Function.comp_def,rename_erase]
  exact erase_event (localVerifier T.rows[e].relation)
    (Complexity.FinalCNFPattern.tableVerifier T) (by decide) (0 : Fin 1) e
    (rename (T,e.val) ∘ Fin.val) Fin.val
    (rename_old T e T.rows[e].relation) (rename_fresh T e T.rows[e].relation) (fun _ => rfl)

 theorem output_correct (T : Table) : output T = targetData (FinalTableFormula.output T) := by
  apply Prod.ext
  · exact (FinalTableFormula.variable_count T).symm
  · change (List.range T.darts).flatMap (fun e => eventData (T,e)) =
      ((List.finRange T.darts).flatMap
        (eventBlock (Complexity.FinalCNFPattern.tableVerifier T) (by decide))).map targetClauseData
    rw [List.map_flatMap]
    have he : (List.finRange T.darts).map Fin.val = List.range T.darts := by
      apply List.ext_getElem
      · simp
      · intro i hi hj; simp
    rw [← he,List.flatMap_map]
    apply List.flatMap_congr
    intro e he
    exact event_correct T e
noncomputable def poly : Poly tableCode FormulaParser.targetCode FinalTableFormula.output :=
  outputPoly.encodeCongr id (fun _ => rfl) (fun T => by
    change FormulaParser.dataCode (output T) = FormulaParser.dataCode (targetData (FinalTableFormula.output T))
    rw [output_correct])
noncomputable def gapPoly (H : RoundTables.BaseTable) :
    Poly FormulaParser.targetCode FormulaParser.targetCode (TableIteration.gapMap H) :=
  (IterationMachine.poly H).comp poly
end VertexCover.Machine.FinalCNFMachine
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
