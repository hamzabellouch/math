import Mathlib
import OAI.Computability.VertexCover.Machines.ParseFormula
import OAI.Computability.VertexCover.Machines.Cloud
import OAI.Computability.VertexCover.Machines.AlphabetFrame
import OAI.Computability.VertexCover.Machines.InitialTable
import OAI.Computability.VertexCover.Machines.FinalCNFBase

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
open PCP PCP.GraphTables FormulaParser TableMachine
abbrev enc := prodBits tableCode natBits
noncomputable def queryPoly : Poly (prodBits enc (finCode (n := 12))) natBits
    (fun p : (Table × ℕ) × Fin 12 => queryName p.1 p.2) := by
  apply Poly.finiteBranch enc finCode natBits (finCode_injective 12)
  intro i
  let c (n : ℕ) := Poly.const enc natBits n
  let first := TableMachine.tailPoly
  let second := ((Poly.fst tableCode natBits).pair TableMachine.reversePoly).comp TableMachine.tailPoly
  by_cases h : i.val<6
  · exact ((((c 6).pair first).comp Poly.natMul).pair (c i.val)).comp Poly.natAdd |>.congr
      (fun x => by simp only [Function.comp_apply,queryName,ite_eq_left h])
  · exact ((((c 6).pair second).comp Poly.natMul).pair (c (i.val-6))).comp Poly.natAdd |>.congr
      (fun x => by simp only [Function.comp_apply,queryName,ite_eq_right h])
abbrev renameEnc := prodBits enc natBits
noncomputable def renameFirst : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.1.1.vertices*6) :=
  ((((Poly.fst enc natBits).comp (Poly.fst tableCode natBits)).comp TableMachine.verticesPoly).pair
    (Poly.const renameEnc natBits 6)).comp Poly.natMul
noncomputable def renameOffset : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.1.2*36864) :=
  (((Poly.fst enc natBits).comp (Poly.snd tableCode natBits)).pair
    (Poly.const renameEnc natBits 36864)).comp Poly.natMul
noncomputable def renameRem : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.2-12) :=
  ((Poly.snd enc natBits).pair (Poly.const renameEnc natBits 12)).comp Poly.natSub
noncomputable def renameNo : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => p.1.1.vertices*6+p.1.2*36864+(p.2-12)) :=
  (((renameFirst.pair renameOffset).comp Poly.natAdd).pair renameRem).comp Poly.natAdd
noncomputable def renameYes : Poly renameEnc natBits
    (fun p : (Table × ℕ) × ℕ => queryName p.1 ⟨p.2%12,Nat.mod_lt _ (by decide)⟩) :=
  ((Poly.fst enc natBits).pair ((Poly.snd enc natBits).comp (Poly.finMod 12 (by decide)))).comp queryPoly
noncomputable def renameTest : Poly renameEnc boolBits
    (fun p : (Table × ℕ) × ℕ => decide (p.2+1≤12)) :=
  ((((Poly.snd enc natBits).comp Poly.natSucc).pair (Poly.const renameEnc natBits 12))).comp Poly.natLE
noncomputable def renamePoly : Poly renameEnc natBits (fun p => rename p.1 p.2) := by
  exact (renameTest.ite renameYes renameNo).congr (fun p => by
    by_cases h : p.2<12
    · have h' : p.2+1≤12 := by omega
      simp only [h',decide_true,ite_true,rename,dite_eq_left h]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt h)
    · have h' : ¬p.2+1≤12 := by omega
      simp only [h',decide_false,Bool.false_eq_true,ite_false,rename,dite_eq_right h]
      rw [PCP.VerifierToCNF.patterns_length]
      rfl)
noncomputable def literalPoly : Poly (prodBits enc unaryLiteralCode) unaryLiteralCode renameLiteral := by
  let s := Poly.fst enc unaryLiteralCode
  let l := Poly.snd enc unaryLiteralCode
  let sign := l.comp (Poly.fst boolBits natBits)
  let idx := l.comp (Poly.snd boolBits natBits)
  exact (sign.pair ((s.pair idx).comp renamePoly)).congr (fun _ => rfl)
noncomputable def clausePoly : Poly (prodBits enc unaryClauseCode) unaryClauseCode renameClause := by
  let s := Poly.fst enc unaryClauseCode
  let cl := Poly.snd enc unaryClauseCode
  let ab := cl.comp (Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  let a := ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)
  let b := ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)
  let c := cl.comp (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  exact (((s.pair a).comp literalPoly).pair ((s.pair b).comp literalPoly)).pair
    ((s.pair c).comp literalPoly)
noncomputable def skeletonPoly : Poly relationCode (listBits unaryClauseCode) skeleton := by
  letI := AlphabetMachine.relationFintype 64
  exact Poly.finite relationCode _ (fun _ _ h => Vector.toList_inj.mp h) skeleton
noncomputable def eventTemplatePoly : Poly enc (listBits unaryClauseCode)
    (fun p : Table × ℕ => skeleton (((tableData p.1).2.getD p.2 rowDefault).2)) := by
  refine (TableMachine.relationPoly.comp skeletonPoly).congr ?_
  intro p
  dsimp only [Function.comp_apply]
noncomputable def eventRenamePoly : Poly (prodBits enc (listBits unaryClauseCode)) (listBits unaryClauseCode)
    (fun p : (Table × ℕ) × List (Triple (Bool × ℕ)) => p.2.map (fun c => renameClause (p.1,c))) :=
  Poly.listMapWith enc unaryClauseCode unaryClauseCode (TableMachine.emptyTable,0)
    InitialTable.clauseDefault InitialTable.clauseDefault clausePoly
noncomputable def eventPoly : Poly enc (listBits unaryClauseCode) eventData :=
  by
  refine (((Poly.identity enc).pair eventTemplatePoly).comp eventRenamePoly).congr ?_
  intro p
  dsimp only [Function.comp_apply,id_eq,eventData]
noncomputable def clausesPoly : Poly tableCode (listBits unaryClauseCode) (fun T => (List.range T.darts).flatMap (fun e => eventData (T,e))) :=
  ((Poly.tabulate tableCode (listBits unaryClauseCode) TableMachine.emptyTable [] TableMachine.dartsPoly eventPoly).comp
    (Poly.listFlatten unaryClauseCode InitialTable.clauseDefault)).congr (fun _ => by simp only [Function.comp_apply,List.flatMap_def])
noncomputable def oldVarsPoly : Poly tableCode natBits (fun T : Table => T.vertices*6) :=
  (TableMachine.verticesPoly.pair (Poly.const tableCode natBits 6)).comp Poly.natMul
noncomputable def newVarsPoly : Poly tableCode natBits (fun T : Table => T.darts*36864) :=
  (TableMachine.dartsPoly.pair (Poly.const tableCode natBits 36864)).comp Poly.natMul
noncomputable def variablesPoly : Poly tableCode natBits (fun T : Table => T.vertices*6+T.darts*36864) :=
  (oldVarsPoly.pair newVarsPoly).comp Poly.natAdd
noncomputable def outputPoly : Poly tableCode FormulaParser.dataCode output := variablesPoly.pair clausesPoly
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
