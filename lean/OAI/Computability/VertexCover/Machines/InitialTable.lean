import Mathlib
import OAI.Computability.VertexCover.PCP.AlphabetRetraction
import OAI.Computability.VertexCover.PCP.RawInitialTables
import OAI.Computability.VertexCover.Machines.DenseParse
import OAI.Computability.VertexCover.Machines.TableBase
import OAI.Computability.VertexCover.Machines.FinCode
import OAI.Computability.VertexCover.Machines.Codec
import OAI.Computability.VertexCover.Machines.Cardinal

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
open PCP PCP.GraphTables
open FormulaParser TableMachine

namespace InitialTable

abbrev ClauseData := Triple (Bool × ℕ)
abbrev Signs := Triple Bool
def signsCode : Signs → List Bool := tripleCode boolBits
def clauseDefault : ClauseData := (((false,0),(false,0)),(false,0))
def signs (cs : ClauseData) : Signs := ((cs.1.1.1,cs.1.2.1),cs.2.1)
def lit (cs : ClauseData) (slot : Fin 3) : Bool × ℕ :=
  if slot=0 then cs.1.1 else if slot=1 then cs.1.2 else cs.2

def accepts (s : Signs) (slot : Fin 3) (a b : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid b &&
    (((PCP.literalValue s.1.1 a.1 || PCP.literalValue s.1.2 a.2.1) ||
      PCP.literalValue s.2 a.2.2) &&
      decide ((if slot=0 then a.1 else if slot=1 then a.2.1 else a.2.2) = b.1))

def relation (p : Signs × (Fin 3 × Bool)) : RelationTable :=
  relationOf (fun a b =>
    let x := AlphabetRetraction.decode64 (RawInitialTables.labelOrder.symm a)
    let y := AlphabetRetraction.decode64 (RawInitialTables.labelOrder.symm b)
    if p.2.2 then accepts p.1 p.2.1 y x else accepts p.1 p.2.1 x y)

def row (p : FormulaData × ℕ) : Row :=
  let F := p.1
  let i := p.2
  let cs := F.2.getD (i/6) clauseDefault
  let slot : Fin 3 := ⟨(i/2)%3,Nat.mod_lt _ (by decide)⟩
  let flip := decide (i%2=1)
  if i < 6*F.2.length then
    ((if flip then (lit cs slot).2 else F.1+i/6,
      if flip then i-1 else i+1),relation (signs cs,(slot,flip)))
  else ((F.1+F.2.length,6*F.2.length),relationOf (fun _ _ => true))

def output (F : FormulaData) : Data :=
  (F.1+F.2.length+1,(List.range (6*F.2.length+1)).map (fun i => row (F,i)))

noncomputable def signsPoly : Poly unaryClauseCode signsCode signs := by
  let ab := Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode
  let a := (ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)).comp (Poly.fst boolBits natBits)
  let b := (ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)).comp (Poly.fst boolBits natBits)
  let c := (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode).comp (Poly.fst boolBits natBits)
  exact (a.pair b).pair c

noncomputable def litPoly : Poly (prodBits unaryClauseCode (finCode (n := 3))) unaryLiteralCode
    (fun p : ClauseData × Fin 3 => lit p.1 p.2) := by
  let cs := Poly.fst unaryClauseCode (finCode (n := 3))
  let slot := Poly.snd unaryClauseCode (finCode (n := 3))
  let test (i : Fin 3) := slot.comp (Poly.finite finCode boolBits (finCode_injective 3) (fun j => decide (j=i)))
  let ab := cs.comp (Poly.fst (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  let a := ab.comp (Poly.fst unaryLiteralCode unaryLiteralCode)
  let b := ab.comp (Poly.snd unaryLiteralCode unaryLiteralCode)
  let c := cs.comp (Poly.snd (prodBits unaryLiteralCode unaryLiteralCode) unaryLiteralCode)
  exact ((test 0).ite a ((test 1).ite b c)).congr (by intro p; simp only [Function.comp_apply,lit,decide_eq_true_eq])

noncomputable def relationPoly : Poly (prodBits signsCode (prodBits (finCode (n := 3)) boolBits))
    relationCode relation :=
  Poly.finite _ _ (prodBits_injective
    (prodBits_injective (prodBits_injective boolBits_injective boolBits_injective) boolBits_injective)
    (prodBits_injective (finCode_injective 3) boolBits_injective)) relation

noncomputable def rowPoly : Poly (prodBits FormulaParser.dataCode natBits) rowCode row := by
  let enc := prodBits FormulaParser.dataCode natBits
  let c (n : ℕ) := Poly.const enc natBits n
  let F := Poly.fst FormulaParser.dataCode natBits
  let i := Poly.snd FormulaParser.dataCode natBits
  let n := F.comp (Poly.fst natBits (listBits unaryClauseCode))
  let clauses := F.comp (Poly.snd natBits (listBits unaryClauseCode))
  let len := clauses.comp (Poly.listLength unaryClauseCode clauseDefault)
  let darts := ((c 6).pair len).comp Poly.natMul
  let j := (i.pair (c 6)).comp Poly.natDiv
  let cs := (j.pair clauses).comp (Poly.listGetD unaryClauseCode clauseDefault)
  let slot := ((i.pair (c 2)).comp Poly.natDiv).comp (Poly.finMod 3 (by decide))
  let flip := (((i.pair (c 2)).comp Poly.natMod).pair (c 1)).comp Poly.natBEq
  let v := ((cs.pair slot).comp litPoly).comp (Poly.snd boolBits natBits)
  let tail := flip.ite v ((n.pair j).comp Poly.natAdd)
  let rev := flip.ite ((i.pair (c 1)).comp Poly.natSub) (i.comp Poly.natSucc)
  let rel := ((cs.comp signsPoly).pair (slot.pair flip)).comp relationPoly
  let normal := (tail.pair rev).pair rel
  let dummy := (((n.pair len).comp Poly.natAdd).pair darts).pair
    (Poly.const enc relationCode (relationOf (fun _ _ => true)))
  let test := (i.pair darts).comp Poly.natLT
  refine (test.ite normal dummy).congr ?_
  intro p
  simp only [Function.comp_apply,row,List.headD_eq_head?_getD,List.head?_drop,
    List.getD_eq_getElem?_getD,decide_eq_true_eq]

noncomputable def outputPoly : Poly FormulaParser.dataCode TableMachine.dataCode output := by
  let n := Poly.fst natBits (listBits unaryClauseCode)
  let len := (Poly.snd natBits (listBits unaryClauseCode)).comp (Poly.listLength unaryClauseCode clauseDefault)
  let darts := (((Poly.const FormulaParser.dataCode natBits 6).pair len).comp Poly.natMul).comp Poly.natSucc
  let rows := Poly.tabulate FormulaParser.dataCode rowCode (0,[]) rowDefault darts rowPoly
  exact (((n.pair len).comp Poly.natAdd).comp Poly.natSucc).pair rows

end InitialTable
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
