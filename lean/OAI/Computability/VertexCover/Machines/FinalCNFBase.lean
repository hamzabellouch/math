import Mathlib
import OAI.Computability.VertexCover.Encoding.FinalCNFPattern
import OAI.Computability.VertexCover.Machines.DenseParse
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

namespace VertexCover.Machine.FinalCNFMachine
open UniqueGames.Foundations
open PCP PCP.VerifierToCNF PCP.GraphTables Target FormulaParser TableMachine

def eraseLiteral {n : ℕ} (f : Fin n → ℕ) (l : Literal n) : Bool × ℕ := (l.positive,f l.variableIndex)
def eraseClause {n : ℕ} (f : Fin n → ℕ) (cl : Clause n) : Triple (Bool × ℕ) :=
  ((eraseLiteral f cl[0],eraseLiteral f cl[1]),eraseLiteral f cl[2])
def splitData : List (Bool × ℕ) → List ℕ → List (Triple (Bool × ℕ))
  | [a,b,c],[] => [((a,b),c)]
  | a::b::rest,y::ys => ((a,b),(true,y))::splitData ((false,y)::rest) ys
  | _,_ => []
 theorem erase_split {n : ℕ} (f : Fin n → ℕ) (ls : List (Literal n)) (ys : List (Fin n)) :
    (splitLong ls ys).map (eraseClause f) = splitData (ls.map (eraseLiteral f)) (ys.map f) := by
  induction ys generalizing ls with
  | nil =>
    cases ls with
    | nil => rfl
    | cons a ls =>
      cases ls with
      | nil => rfl
      | cons b ls =>
        cases ls with
        | nil => rfl
        | cons c ls => cases ls <;> rfl
  | cons y ys ih =>
    cases ls with
    | nil => rfl
    | cons a ls =>
      cases ls with
      | nil => rfl
      | cons b rest =>
        simpa [splitLong,eraseClause,eraseLiteral,splitData] using
          congrArg (List.cons ((eraseLiteral f a,eraseLiteral f b),(true,f y)))
            (ih (⟨y,false⟩::rest))

 theorem erase_block {q : ℕ} (V W : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (e' : Fin W.events) (p : PatternIndex q)
    (f : Fin (outputVariables V) → ℕ) (g : Fin (outputVariables W) → ℕ)
    (hquery : ∀ i, f (oldIndex V (V.query e i)) = g (oldIndex W (W.query e' i)))
    (hfresh : ∀ j, f (freshIndex V e p j) = g (freshIndex W e' p j))
    (haccept : V.accepts e (patternAt q p) = W.accepts e' (patternAt q p)) :
    (block V hq e p).map (eraseClause f) = (block W hq e' p).map (eraseClause g) := by
  unfold block
  rw [haccept]
  split
  · rw [List.map_replicate,List.map_replicate]
    congr 1
    simp [tautology,eraseClause,eraseLiteral,hquery]
  · rw [erase_split,erase_split]
    congr 1
    · simp only [forbiddenClause,List.map_ofFn]
      congr 1
      funext i
      exact Prod.ext rfl (hquery i)
    · simp only [auxiliaryNames,List.map_ofFn]
      congr 1
      funext j
      exact hfresh j

theorem oldIndex_value {q : ℕ} (V : FiniteVerifier q) (i : Fin V.variables) :
    (oldIndex V i).val = i.val := rfl

theorem erase_event {q : ℕ} (V W : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (e' : Fin W.events)
    (f : Fin (outputVariables V) → ℕ) (g : Fin (outputVariables W) → ℕ)
    (hquery : ∀ i, f (oldIndex V (V.query e i)) = g (oldIndex W (W.query e' i)))
    (hfresh : ∀ p j, f (freshIndex V e p j) = g (freshIndex W e' p j))
    (haccept : ∀ p, V.accepts e (patternAt q p) = W.accepts e' (patternAt q p)) :
    (eventBlock V hq e).map (eraseClause f) = (eventBlock W hq e').map (eraseClause g) := by
  simp only [eventBlock,List.map_flatMap]
  apply List.flatMap_congr
  intro p _
  exact erase_block V W hq e e' p f g hquery (hfresh p) (haccept p)

abbrev Shapes := 12+1*(patterns 12).length*(12-3)
def localVerifier (r : RelationTable) : FiniteVerifier 12 where
  «variables» := 12
  events := 1
  query := fun _ i => i
  accepts := fun _ bits => r[Complexity.FinalCNFPattern.relationAddress bits]
def skeleton (r : RelationTable) : List (Triple (Bool × ℕ)) :=
  (eventBlock (localVerifier r) (by decide) (0 : Fin 1)).map (eraseClause Fin.val)

def queryName (p : GraphTables.Table × ℕ) (i : Fin 12) : ℕ :=
  let rows := (tableData p.1).2
  let row := rows.getD p.2 rowDefault
  if i.val<6 then 6*row.1.1+i.val
  else 6*(rows.getD row.1.2 rowDefault).1.1+(i.val-6)

def rename (p : GraphTables.Table × ℕ) (j : ℕ) : ℕ :=
  if h : j<12 then queryName p ⟨j,h⟩
  else p.1.vertices*6+p.2*((patterns 12).length*9)+(j-12)
def renameLiteral (p : (GraphTables.Table × ℕ) × (Bool × ℕ)) : Bool × ℕ :=
  (p.2.1,rename p.1 p.2.2)
def renameClause (p : (GraphTables.Table × ℕ) × Triple (Bool × ℕ)) : Triple (Bool × ℕ) :=
  ((renameLiteral (p.1,p.2.1.1),renameLiteral (p.1,p.2.1.2)),renameLiteral (p.1,p.2.2))
theorem rename_erase {n : ℕ} (p : Table × ℕ) (cl : Clause n) :
    renameClause (p,eraseClause Fin.val cl) = eraseClause (rename p ∘ Fin.val) cl := rfl

def eventData (p : GraphTables.Table × ℕ) : List (Triple (Bool × ℕ)) :=
  (skeleton (((tableData p.1).2.getD p.2 rowDefault).2)).map (fun c => renameClause (p,c))
def output (T : GraphTables.Table) : FormulaData :=
  (T.vertices*6+T.darts*36864,(List.range T.darts).flatMap (fun e => eventData (T,e)))

 theorem queryName_correct (T : GraphTables.Table) (e : Fin T.darts) (i : Fin 12) :
    queryName (T,e.val) i = ((Complexity.FinalCNFPattern.tableVerifier T).query e i).val := by
  refine Fin.addCases (m := 6) (n := 6) ?_ ?_ i
  · intro j
    have hj := j.isLt
    simp only [queryName,lookup_valid,Fin.val_castAdd,ite_eq_left hj]
    rw [Fin.addCases_left]
    simp [FinalBooleanVerifier.bitIndex,finProdFinEquiv,rowData,Nat.add_comm]
  · intro j
    have hj : ¬6+j.val<6 := by omega
    simp only [queryName,lookup_valid,Fin.val_natAdd,ite_eq_right hj]
    change 6*((tableData T).2.getD T.rows[e].reverseIndex.val rowDefault).1.1+(6+j.val-6) = _
    rw [lookup_valid]
    rw [Fin.addCases_right]
    simp [FinalBooleanVerifier.bitIndex,finProdFinEquiv,rowData,Nat.add_comm,
      ConstraintGraph.head,Complexity.FinalCNFPattern.tableGraph]
    rfl

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
