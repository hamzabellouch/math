import Mathlib
import OAI.Computability.VertexCover.Reduction.DenseEncodingBound
import OAI.Computability.VertexCover.Machines.ParseClause
import OAI.Computability.VertexCover.Machines.ListIndex

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
namespace FormulaParser
open UniqueGames.BinaryFormula
open UniqueGames.Foundations

abbrev Triple (α : Type) := (α × α) × α
abbrev tripleCode {α : Type} (e : α → List Bool) : Triple α → List Bool := prodBits (prodBits e e) e

def literalData (l : Literal) : Bool × ℕ := (l.positive,l.name)
def clauseData (clause : Clause) : Triple (Bool × ℕ) :=
  ((literalData clause[0],literalData clause[1]),literalData clause[2])
def unaryLiteralCode : Bool × ℕ → List Bool := prodBits boolBits natBits
def unaryClauseCode : Triple (Bool × ℕ) → List Bool := tripleCode unaryLiteralCode
abbrev FormulaData := ℕ × List (Triple (Bool × ℕ))
def dataCode : FormulaData → List Bool := prodBits natBits (listBits unaryClauseCode)

def targetLiteralData {n : ℕ} (l : Target.Literal n) : Bool × ℕ :=
  (l.positive,l.variableIndex.val)
def targetClauseData {n : ℕ} (clause : Target.Clause n) : Triple (Bool × ℕ) :=
  ((targetLiteralData clause[0],targetLiteralData clause[1]),targetLiteralData clause[2])
def targetData (F : Target.Formula) : FormulaData :=
  (F.variables,F.clauses.map targetClauseData)
def targetCode (F : Target.Formula) : List Bool := dataCode (targetData F)

noncomputable def literalNamePoly : Poly literalCode Nat.bits (fun l => l.name) :=
  (Poly.snd boolBits Nat.bits).encodeCongr literalData (fun _ => rfl) (fun _ => rfl)

noncomputable def literalSignPoly : Poly literalCode boolBits (fun l => l.positive) :=
  (Poly.fst boolBits Nat.bits).encodeCongr literalData (fun _ => rfl) (fun _ => rfl)

noncomputable def clauseGetPoly (i : Fin 3) : Poly clauseCode literalCode (fun clause => clause[i]) := by
  by_cases h₀ : i = 0
  · subst i
    exact (((Poly.fst (prodBits literalCode literalCode) literalCode).comp
      (Poly.fst literalCode literalCode)).encodeCongr (fun clause => ((clause[0],clause[1]),clause[2]))
      (fun _ => rfl) (fun _ => rfl))
  · by_cases h₁ : i = 1
    · subst i
      exact (((Poly.fst (prodBits literalCode literalCode) literalCode).comp
      (Poly.snd literalCode literalCode)).encodeCongr (fun clause => ((clause[0],clause[1]),clause[2]))
      (fun _ => rfl) (fun _ => rfl))
    · have h₂ : i = 2 := by omega
      subst i
      exact (Poly.snd (prodBits literalCode literalCode) literalCode).encodeCongr
        (fun clause => ((clause[0],clause[1]),clause[2])) (fun _ => rfl) (fun _ => rfl)

noncomputable def clauseNamesPoly : Poly clauseCode (listBits Nat.bits) clauseNames := by
  let n₀ := (clauseGetPoly 0).comp literalNamePoly
  let n₁ := (clauseGetPoly 1).comp literalNamePoly
  let n₂ := (clauseGetPoly 2).comp literalNamePoly
  let empty := Poly.const clauseCode (listBits Nat.bits) []
  let c₂ := (n₂.pair empty).comp (Poly.listCons Nat.bits)
  let c₁ := (n₁.pair c₂).comp (Poly.listCons Nat.bits)
  exact ((n₀.pair c₁).comp (Poly.listCons Nat.bits)).congr (fun _ => rfl)

noncomputable def sourceNamesPoly : Poly formulaCode (listBits Nat.bits) sourceNames :=
  (Poly.listFlatMap clauseCode Nat.bits clauseDefault 0 clauseNamesPoly).encodeCongr
    Formula.clauses (fun _ => rfl) (fun _ => rfl)

noncomputable def activeNamesPoly : Poly formulaCode (listBits Nat.bits) activeNames :=
  sourceNamesPoly.comp (Poly.eraseDups Nat.bits 0 Poly.bitsNatEq)

def compactDataLiteral (p : List ℕ × Literal) : Bool × ℕ :=
  (p.2.positive,p.1.idxOf p.2.name)

def compactDataClause (p : List ℕ × Clause) : Triple (Bool × ℕ) :=
  ((compactDataLiteral (p.1,p.2[0]),compactDataLiteral (p.1,p.2[1])),compactDataLiteral (p.1,p.2[2]))

def denseData (F : Formula) : FormulaData :=
  ((activeNames F).length,F.clauses.map fun clause => compactDataClause (activeNames F,clause))

noncomputable def compactLiteralPoly : Poly (prodBits (listBits Nat.bits) literalCode)
    unaryLiteralCode compactDataLiteral := by
  let names := Poly.fst (listBits Nat.bits) literalCode
  let lit := Poly.snd (listBits Nat.bits) literalCode
  let idx := (((lit.comp literalNamePoly).pair names).comp (Poly.listIdxOf Nat.bits 0 Poly.bitsNatEq))
  exact ((lit.comp literalSignPoly).pair idx).congr (fun _ => rfl)

noncomputable def compactClausePoly : Poly (prodBits (listBits Nat.bits) clauseCode)
    unaryClauseCode compactDataClause := by
  let names := Poly.fst (listBits Nat.bits) clauseCode
  let clause := Poly.snd (listBits Nat.bits) clauseCode
  let lit (i : Fin 3) := (names.pair (clause.comp (clauseGetPoly i))).comp compactLiteralPoly
  exact ((lit 0).pair (lit 1)).pair (lit 2)

noncomputable def denseDataPoly : Poly formulaCode dataCode denseData := by
  let names := activeNamesPoly
  let count := names.comp (Poly.listLength Nat.bits 0)
  let clauses : Poly formulaCode (listBits clauseCode) Formula.clauses :=
    (Poly.identity (listBits clauseCode)).encodeCongr Formula.clauses (fun _ => rfl) (fun _ => rfl)
  let cs := (names.pair clauses).comp (Poly.listMapWith (listBits Nat.bits) clauseCode
    unaryClauseCode [] clauseDefault (((false,0),(false,0)),(false,0)) compactClausePoly)
  exact count.pair cs

 theorem denseData_eq (F : Formula) : denseData F = targetData (dense F) := by
  apply Prod.ext
  · rfl
  · simp only [denseData,targetData,dense,compactClauses,List.map_map]
    change F.clauses.map (fun clause => compactDataClause (activeNames F,clause)) =
      F.clauses.attach.map (fun clause => compactDataClause (activeNames F,clause.val))
    exact List.attach_map_val.symm

noncomputable def densePoly : Poly formulaCode targetCode dense :=
  denseDataPoly.encodeCongr id (fun _ => rfl) (fun F => by
    change dataCode (denseData F) = dataCode (targetData (dense F))
    rw [denseData_eq])

end FormulaParser
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
