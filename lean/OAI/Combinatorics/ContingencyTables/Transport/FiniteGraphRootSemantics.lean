import OAI.Combinatorics.ContingencyTables.Machines.FiniteGraphRootProgram

namespace OAI

/-! # Exact correctness of the finite component-root program

The stored adjacency list is identified with the given finite graph.
Each list growth round is the proved finite reachability growth, and
the final binary minimum is the least vertex of the actual component.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def adjacencyRow (b : Fin n) : List ℕ :=
  ((List.finRange n).filter (fun a => decide (G.Adj a b))).map Fin.val

def graphCode : GraphCode := List.ofFn (adjacencyRow G)

lemma graphCode_length : (graphCode G).length=n := List.length_ofFn

lemma graphCode_getD (b : Fin n) : (graphCode G).getD b.val []=adjacencyRow G b := by
  simp only [graphCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,b.isLt,dite_eq_left,
    Option.getD_some]

lemma adjacencyRow_mem (b : Fin n) (a : ℕ) :
    a∈adjacencyRow G b ↔ ∃ u : Fin n,u.val=a ∧ G.Adj u b := by
  simp only [adjacencyRow,List.mem_map,List.mem_filter,List.mem_finRange,true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u,hu,ha⟩
    exact ⟨u,ha,hu⟩
  · rintro ⟨u,ha,hu⟩
    exact ⟨u,hu,ha⟩

lemma grow_mem (s : List ℕ) (b : Fin n) :
    b.val∈grow (graphCode G,s) ↔
      b.val∈s ∨ ∃ a : Fin n,a.val∈s ∧ G.Adj a b := by
  simp only [grow,indices,List.mem_filter,List.mem_range,graphCode_length,growTest,
    Bool.or_eq_true,decide_eq_true_eq,neighborHit,List.any_eq_true,graphCode_getD,
    b.isLt,true_and]
  constructor
  · rintro (h|⟨a,ha,hs⟩)
    · exact Or.inl h
    · obtain ⟨u,hu,hg⟩ := (adjacencyRow_mem G b a).mp ha
      exact Or.inr ⟨u,hu.symm ▸ hs,hg⟩
  · rintro (h|⟨a,ha,hg⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a.val,(adjacencyRow_mem G b a.val).mpr ⟨a,rfl,hg⟩,ha⟩

lemma grow_bound (rows : GraphCode) (s : List ℕ) {a : ℕ}
    (ha : a∈grow (rows,s)) : a<rows.length := by
  exact List.mem_range.mp (List.mem_of_mem_filter ha)

lemma fold_advance (steps : List (List ℕ)) (rows : GraphCode) (s : List ℕ) :
    (steps.foldl (fun s row => advance (row,s)) (rows,s)).2=
      (fun s => grow (rows,s))^[steps.length] s := by
  induction steps generalizing s with
  | nil => rfl
  | cons row steps ih =>
    simp only [List.foldl_cons,List.length_cons]
    change (steps.foldl (fun s row => advance (row,s)) (rows,grow (rows,s))).2=_
    rw [ih,Function.iterate_succ_apply]

lemma iterate_mem (v b : Fin n) (k : ℕ) :
    b.val∈(fun s => grow (graphCode G,s))^[k] [v.val] ↔
      b∈MatchingFPRAS.ComputableReach.reached G {v} k := by
  induction k generalizing b with
  | zero =>
    simp only [Function.iterate_zero_apply,List.mem_singleton,
      MatchingFPRAS.ComputableReach.reached,Finset.mem_singleton]
    exact Fin.ext_iff.symm
  | succ k ih =>
    rw [Function.iterate_succ_apply',grow_mem,
      MatchingFPRAS.ComputableReach.reached_step,mem_grow]
    simp only [ih]

lemma iterate_bound (v : Fin n) (k : ℕ) :
    ∀ a∈(fun s => grow (graphCode G,s))^[k] [v.val],a<n := by
  cases k with
  | zero =>
    intro a ha
    simp only [Function.iterate_zero_apply,List.mem_singleton] at ha
    exact ha ▸ v.isLt
  | succ k =>
    intro a ha
    rw [Function.iterate_succ_apply'] at ha
    simpa only [graphCode_length] using grow_bound _ _ ha

lemma reached_eq_iterate (v : Fin n) :
    reached (graphCode G,v.val)=(fun s => grow (graphCode G,s))^[n] [v.val] := by
  unfold reached run
  rw [fold_advance,graphCode_length]

theorem reached_mem_iff (v b : Fin n) :
    b.val∈reached (graphCode G,v.val) ↔ G.Reachable v b := by
  rw [reached_eq_iterate,iterate_mem]
  simpa only [MatchingFPRAS.ComputableReach.closure,Fintype.card_fin] using mem_closure G v b

lemma reached_bound (v : Fin n) {a : ℕ} (ha : a∈reached (graphCode G,v.val)) : a<n := by
  rw [reached_eq_iterate] at ha
  exact iterate_bound G v n a ha

lemma minimum_fold_le_of_mem (xs : List ℕ) (b a : ℕ) (ha : a∈xs) :
    xs.foldl (fun b a => min a b) b≤a := by
  induction xs generalizing b with
  | nil => simp only [List.not_mem_nil] at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with h|ha
    · subst x
      exact (minimum_fold_le xs (min a b)).trans (min_le_left _ _)
    · exact ih (min x b) ha

lemma le_minimum_fold (xs : List ℕ) (b a : ℕ) (hb : a≤b)
    (hs : ∀ x∈xs,a≤x) : a≤xs.foldl (fun b x => min x b) b := by
  induction xs generalizing b with
  | nil => exact hb
  | cons x xs ih =>
    exact ih (min x b) (le_min (hs x (by simp)) hb)
      (fun y hy => hs y (by simp [hy]))

/-- The executed least root agrees with the explicit mathematical
selector. It does not identify that selector with a quotient choice. -/
theorem rootCode_eq (v : Fin n) :
    rootCode (graphCode G,v.val)=(FiniteGraphRoots.root G v).val := by
  unfold rootCode
  rw [graphCode_length]
  apply le_antisymm
  · exact minimum_fold_le_of_mem _ _ _ ((reached_mem_iff G v _).mpr
      (FiniteGraphRoots.root_reachable G v))
  · apply le_minimum_fold _ _ _ (FiniteGraphRoots.root G v).isLt.le
    intro a ha
    let u : Fin n := ⟨a,reached_bound G v ha⟩
    have hr : G.Reachable v u := (reached_mem_iff G v u).mp ha
    exact FiniteGraphRoots.root_le G hr

end ContingencyTables.FiniteGraphRootProgram

end OAI
