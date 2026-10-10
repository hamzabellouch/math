import OAI.Combinatorics.ContingencyTables.Sampling.GreedyCellMachine
import OAI.Combinatorics.MatchingCount.Machines.TreeFold

namespace OAI

/-! # A binary list program for one row of the greedy initializer -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

abbrev RowAccumulator := ℕ × (List ℕ × List ℕ)

/-- A row pass keeps its residual margin and builds both output lists
in reverse order, using only binary minimum, subtraction and list cons. -/
def rowCell (z : ℕ × RowAccumulator) : RowAccumulator :=
  let q := min z.2.1 z.1
  (z.2.1-q,(q::z.2.2.1,(z.1-q)::z.2.2.2))

def rowCellRealizer : Realizer rowCell := by
  let A : Realizer (fun z : ℕ × RowAccumulator => z.2.1) := composition second first
  let C : Realizer (fun z : ℕ × RowAccumulator => z.1) := first
  let Q := composition (pair A C) minimum
  let X : Realizer (fun z : ℕ × RowAccumulator => z.2.2.1) :=
    composition (composition second second) first
  let Y : Realizer (fun z : ℕ × RowAccumulator => z.2.2.2) :=
    composition (composition second second) second
  exact (pair (composition (pair A Q) subtract)
    (pair (composition (pair Q X) listCons)
      (composition (pair (composition (pair C Q) subtract) Y) listCons))).congr (fun _ => rfl)

/-- The list version of the already proved dimension-recursive row split. -/
def listSplitRow : ℕ → List ℕ → RowAccumulator
  | a,[] => (a,([],[]))
  | a,c::cs =>
    let q := min a c
    let tail := listSplitRow (a-q) cs
    (tail.1,(q::tail.2.1,(c-q)::tail.2.2))

lemma fold_rowCell (cs : List ℕ) (a : ℕ) (xs ys : List ℕ) :
    cs.foldl (fun z c => rowCell (c,z)) (a,(xs,ys))=
      let tail := listSplitRow a cs
      (tail.1,(tail.2.1.reverse++xs,tail.2.2.reverse++ys)) := by
  induction cs generalizing a xs ys with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons]
    change cs.foldl (fun z c => rowCell (c,z))
      (a-min a c,(min a c::xs,(c-min a c)::ys))=_
    rw [ih]
    simp only [listSplitRow,List.reverse_cons,List.append_assoc,List.singleton_append]

def rowSplitRealizer : Realizer (fun z : ℕ × List ℕ => listSplitRow z.1 z.2) := by
  let start : Realizer (fun z : ℕ × List ℕ => (z.2,(z.1,(([] : List ℕ),([] : List ℕ))))) :=
    pair second (pair first (constant ([],[])))
  let finish : Realizer (fun z : RowAccumulator => (z.1,(z.2.1.reverse,z.2.2.reverse))) :=
    pair first (pair (composition (composition second first) reverse)
      (composition (composition second second) reverse))
  exact (composition (composition start (fold rowCellRealizer)) finish).congr (by
    intro z
    change (fun v : RowAccumulator => (v.1,(v.2.1.reverse,v.2.2.reverse)))
      (z.2.foldl (fun s c => rowCell (c,s)) (z.1,([],[])))=listSplitRow z.1 z.2
    rw [fold_rowCell]
    simp)

lemma listSplitRow_balance (a : ℕ) (cs : List ℕ) :
    (listSplitRow a cs).2.1.sum+(listSplitRow a cs).1=a := by
  induction cs generalizing a with
  | nil => simp [listSplitRow]
  | cons c cs ih =>
    simp only [listSplitRow,List.sum_cons]
    have ht := ih (a-min a c)
    have hq := min_le_left a c
    omega

lemma listSplitRow_lengths (a : ℕ) (cs : List ℕ) :
    (listSplitRow a cs).2.1.length=cs.length ∧
      (listSplitRow a cs).2.2.length=cs.length := by
  induction cs generalizing a with
  | nil => exact ⟨rfl,rfl⟩
  | cons c cs ih =>
    constructor
    · simpa only [listSplitRow,List.length_cons] using congrArg Nat.succ (ih (a-min a c)).1
    · simpa only [listSplitRow,List.length_cons] using congrArg Nat.succ (ih (a-min a c)).2

end ContingencyTables.GreedyFeasibleTable

end OAI
