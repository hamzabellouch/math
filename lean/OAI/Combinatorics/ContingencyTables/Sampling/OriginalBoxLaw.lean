import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableBox
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLaw

namespace OAI

/-! # Embedding original-table laws in their computed finite box -/

namespace ContingencyTables.OriginalBoxLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
open OriginalTableBox

lemma tableAt_index (hN : (∑ i,r i)≤N) (X : Table r c) :
    tableAt r c (index r c hN X)=some X :=
  (tableAt_eq_some r c hN _ X).mpr rfl

lemma index_eq_iff (hN : (∑ i,r i)≤N) (X Y : Table r c) :
    index r c hN X=index r c hN Y ↔ X=Y := by
  constructor
  · intro h
    have he := congrArg (tableAt r c) h
    rw [tableAt_index,tableAt_index] at he
    exact Option.some.inj he
  · rintro rfl
    rfl

def law (hN : (∑ i,r i)≤N) (p : IntegerLaw (Option (Table r c)) Q) :
    IntegerLaw (Option (Index m n N)) Q :=
  p.push (Option.map (index r c hN))

lemma count_none (hN : (∑ i,r i)≤N) (p : IntegerLaw (Option (Table r c)) Q) :
    (law r c hN p).count none=p.count none := by
  simp [law,IntegerLaw.push,Fintype.sum_option]

/-- Invalid box entries have zero count; every valid completion has
exactly the count of its unique feasible table. -/
lemma count_some (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (k : Index m n N) :
    (law r c hN p).count (some k)=
      (tableAt r c k).elim 0 (fun X => p.count (some X)) := by
  simp only [law,IntegerLaw.push,Fintype.sum_option,Option.map_none,reduceCtorEq,
    ite_false,zero_add,Option.map_some,Option.some.injEq]
  simp_rw [←tableAt_eq_some r c hN]
  cases tableAt r c k <;> simp

lemma count_index (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (X : Table r c) :
    (law r c hN p).count (some (index r c hN X))=p.count (some X) := by
  rw [count_some r c,tableAt_index]
  rfl

/-- Embedding tables into the explicit finite candidate list commutes
with every bounded first-success retry. -/
theorem retry_count_index (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (fallback X : Table r c) (J : ℕ) :
    ((law r c hN p).retry (index r c hN fallback) J).count (index r c hN X)=
      (p.retry fallback J).count X := by
  change IntegerLaw.retryCount (law r c hN p) (index r c hN fallback) J (index r c hN X)=
    IntegerLaw.retryCount p fallback J X
  induction J with
  | zero => simp only [IntegerLaw.retryCount,index_eq_iff r c]
  | succ J ih =>
    rw [IntegerLaw.retryCount,IntegerLaw.retryCount,count_index r c,count_none,ih]

/-- A retry keeps every invalid finite-box entry at zero. -/
lemma retry_count_some (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (fallback : Table r c) (J : ℕ)
    (k : Index m n N) :
    ((law r c hN p).retry (index r c hN fallback) J).count k=
      (tableAt r c k).elim 0 (fun T => (p.retry fallback J).count T) := by
  cases hk : tableAt r c k with
  | none =>
    have hi : k≠index r c hN fallback := by
      intro he
      rw [he,tableAt_index] at hk
      cases hk
    change IntegerLaw.retryCount (law r c hN p) (index r c hN fallback) J k=0
    induction J with
    | zero => simp only [IntegerLaw.retryCount,hi,ite_false]
    | succ J ih =>
      rw [IntegerLaw.retryCount,count_some r c hN,hk,ih]
      simp
  | some T =>
    have he := (tableAt_eq_some r c hN k T).mp hk
    rw [←he]
    exact retry_count_index r c hN p fallback T J

end
end ContingencyTables.OriginalBoxLaw

end OAI
