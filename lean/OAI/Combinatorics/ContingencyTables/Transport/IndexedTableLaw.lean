import OAI.Combinatorics.ContingencyTables.Transport.BoxCompletion
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLaw

namespace OAI

/-! # Embedding accepted-table laws into the computed completion list -/

namespace ContingencyTables.IndexedTableLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)

abbrev Index (m n N : ℕ) := Fin ((N+1)^(m*n))

def index (hN : (∑ i,R i)≤N) (X : Table R P) : Index m n N :=
  finFunctionFinEquiv (BoxCompletion.encode R P hN X)

def tableAt (htotal : ∑ i,R i=∑ j,P j) (k : Index m n N) : Option (Table R P) :=
  BoxCompletion.decode R P htotal N (finFunctionFinEquiv.symm k)

lemma tableAt_eq_some (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (k : Index m n N) (X : Table R P) :
    tableAt R P htotal k=some X ↔ index R P hN X=k := by
  rw [tableAt,BoxCompletion.decode_eq_some R P htotal hN]
  constructor
  · intro h
    have he := congrArg finFunctionFinEquiv h
    simpa only [Equiv.apply_symm_apply,index] using he.symm
  · intro h
    rw [←h,index,Equiv.symm_apply_apply]

lemma tableAt_index (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (X : Table R P) : tableAt R P htotal (index R P hN X)=some X :=
  (tableAt_eq_some R P htotal hN _ X).mpr rfl

lemma index_eq_iff (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (X Y : Table R P) : index R P hN X=index R P hN Y ↔ X=Y := by
  constructor
  · intro h
    have he := congrArg (tableAt R P htotal) h
    rw [tableAt_index,tableAt_index] at he
    exact Option.some.inj he
  · rintro rfl
    rfl

def law (hN : (∑ i,R i)≤N) (p : IntegerLaw (Option (Table R P)) Q) :
    IntegerLaw (Option (Index m n N)) Q :=
  p.push (Option.map (index R P hN))

lemma count_none (hN : (∑ i,R i)≤N) (p : IntegerLaw (Option (Table R P)) Q) :
    (law R P hN p).count none=p.count none := by
  simp [law,IntegerLaw.push,Fintype.sum_option]

/-- Invalid completions have zero count; every valid completion has
exactly the count of its unique feasible table. -/
lemma count_some (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (p : IntegerLaw (Option (Table R P)) Q) (k : Index m n N) :
    (law R P hN p).count (some k)=
      (tableAt R P htotal k).elim 0 (fun X => p.count (some X)) := by
  simp only [law,IntegerLaw.push,Fintype.sum_option,Option.map_none,reduceCtorEq,
    ite_false,zero_add,Option.map_some,Option.some.injEq]
  simp_rw [←tableAt_eq_some R P htotal hN]
  cases tableAt R P htotal k <;> simp

lemma count_index (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (p : IntegerLaw (Option (Table R P)) Q) (X : Table R P) :
    (law R P hN p).count (some (index R P hN X))=p.count (some X) := by
  rw [count_some R P htotal,tableAt_index]
  rfl

/-- Embedding tables into the explicit finite candidate list commutes
with every bounded first-success retry. -/
theorem retry_count_index (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (p : IntegerLaw (Option (Table R P)) Q) (fallback X : Table R P) (J : ℕ) :
    ((law R P hN p).retry (index R P hN fallback) J).count (index R P hN X)=
      (p.retry fallback J).count X := by
  change IntegerLaw.retryCount (law R P hN p) (index R P hN fallback) J (index R P hN X)=
    IntegerLaw.retryCount p fallback J X
  induction J with
  | zero => simp only [IntegerLaw.retryCount,index_eq_iff R P htotal]
  | succ J ih =>
    rw [IntegerLaw.retryCount,IntegerLaw.retryCount,count_index R P htotal,count_none,ih]

end
end ContingencyTables.IndexedTableLaw

end OAI
