import OAI.Combinatorics.ContingencyTables.Sampling.GreedyRowMachine

namespace OAI

/-! # A fixed binary list program constructing the greedy table -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

abbrev TableAccumulator := List ℕ × List (List ℕ)

def tableRow (z : ℕ × TableAccumulator) : TableAccumulator :=
  let row := listSplitRow z.1 z.2.1
  (row.2.2,row.2.1::z.2.2)

def tableRowRealizer : Realizer tableRow := by
  let row : Realizer (fun z : ℕ × TableAccumulator => listSplitRow z.1 z.2.1) :=
    composition (pair first (composition second first)) rowSplitRealizer
  exact (pair (composition (composition row second) second)
    (composition (pair (composition (composition row second) first)
      (composition second second)) listCons)).congr (fun _ => rfl)

def listMatrix : List ℕ → List ℕ → List (List ℕ)
  | [],_ => []
  | a::as,cs =>
    let row := listSplitRow a cs
    row.2.1::listMatrix as row.2.2

lemma fold_tableRow (rs cs : List ℕ) (rows : List (List ℕ)) :
    (rs.foldl (fun z a => tableRow (a,z)) (cs,rows)).2=
      (listMatrix rs cs).reverse++rows := by
  induction rs generalizing cs rows with
  | nil => rfl
  | cons a rs ih =>
    rw [List.foldl_cons]
    change (rs.foldl (fun z a => tableRow (a,z))
      ((listSplitRow a cs).2.2,(listSplitRow a cs).2.1::rows)).2=_
    rw [ih]
    simp only [listMatrix,List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Every loop is over an input row or column; binary margins are never
counted down one unit at a time. -/
def tableRealizer : Realizer (fun z : List ℕ × List ℕ => listMatrix z.1 z.2) := by
  let start : Realizer (fun z : List ℕ × List ℕ => (z.1,(z.2,([] : List (List ℕ))))) :=
    pair first (pair second (constant []))
  exact (composition (composition (composition start (fold tableRowRealizer)) second) reverse).congr (by
    intro z
    change ((z.1.foldl (fun s a => tableRow (a,s)) (z.2,[])).2).reverse=_
    rw [fold_tableRow]
    simp)

lemma listSplitRow_ofFn {n : ℕ} (a : ℕ) (cs : Fin n → ℕ) :
    listSplitRow a (List.ofFn cs)=
      ((splitRow a cs).unused,
        (List.ofFn (splitRow a cs).assigned,List.ofFn (splitRow a cs).remaining)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ,listSplitRow,splitRow,ih,Fin.cons_zero,Fin.cons_succ]

/-- The compiled list program computes the same feasible matrix used
by the probability analysis. -/
theorem listMatrix_ofFn {m n : ℕ} (rs : Fin m → ℕ) (cs : Fin n → ℕ) :
    listMatrix (List.ofFn rs) (List.ofFn cs)=
      List.ofFn (fun i => List.ofFn (matrix rs cs i)) := by
  induction m generalizing cs with
  | zero => rfl
  | succ m ih =>
    simp only [List.ofFn_succ,listMatrix,listSplitRow_ofFn,ih,matrix,Fin.cons_zero,
      Fin.cons_succ]

end ContingencyTables.GreedyFeasibleTable

end OAI
