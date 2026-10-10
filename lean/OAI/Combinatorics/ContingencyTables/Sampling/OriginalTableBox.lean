import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableEnumeration

namespace OAI

/-! # The full original-table box and its unique feasible entries -/

namespace ContingencyTables.OriginalTableBox
open DensePrograms ProfilePrograms
open scoped BigOperators Classical
noncomputable section

abbrev Box (m n N : ℕ) := Fin (m*n) → Fin (N+1)
abbrev Index (m n N : ℕ) := Fin ((N+1)^(m*n))

def matrix {m n N : ℕ} (z : Box m n N) : Fin m → Fin n → ℕ :=
  fun i j => (z (finProdFinEquiv (i,j))).val

def decode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (z : Box m n N) : Option (Table r c) :=
  if h : HasMargins (matrix z) r c then some ⟨matrix z,h⟩ else none

def encode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : Box m n N := fun k =>
  ⟨T.val (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2,
    Nat.lt_succ_of_le ((entry_le_total T.property _ _).trans hN)⟩

lemma matrix_encode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : matrix (encode r c hN T)=T.val := by
  funext i j
  simp only [matrix,encode,Equiv.symm_apply_apply]

lemma decode_encode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : decode r c (encode r c hN T)=some T := by
  unfold decode
  rw [matrix_encode]
  simp only [T.property,dite_true]
  rfl

lemma decode_eq_some {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (z : Box m n N) (T : Table r c) :
    decode r c z=some T ↔ z=encode r c hN T := by
  constructor
  · intro ht
    unfold decode at ht
    split at ht
    next hm =>
      have he := congrArg Subtype.val (Option.some.inj ht)
      funext k
      apply Fin.ext
      have hk := congrFun (congrFun he (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
      simpa only [matrix,encode,Equiv.apply_symm_apply,Prod.mk.eta] using hk
    next hm => cases ht
  · rintro rfl
    exact decode_encode r c hN T

def index {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : Index m n N := finFunctionFinEquiv (encode r c hN T)

def tableAt {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : Index m n N) :
    Option (Table r c) := decode r c (finFunctionFinEquiv.symm k)

lemma tableAt_eq_some {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (k : Index m n N) (T : Table r c) :
    tableAt r c k=some T ↔ index r c hN T=k := by
  rw [tableAt,decode_eq_some r c hN]
  constructor
  · intro he
    have hh := congrArg finFunctionFinEquiv he
    simpa only [Equiv.apply_symm_apply,index] using hh.symm
  · intro he
    rw [←he,index,Equiv.symm_apply_apply]

lemma freeMatrix_code {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (z : Box m n N) :
    originalFreeMatrix ((List.ofFn r,List.ofFn c),List.ofFn (fun i => (z i).val))=
      matrixCode (matrix z) := by
  exact unflattenGrid_code (fun i : Option (Fin m) => i.elim 0 r)
    (fun j : Option (Fin n) => j.elim 0 c) (fun i => (z i).val)

lemma candidate_code {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (z : Box m n N) :
    originalCandidate ((List.ofFn r,List.ofFn c),List.ofFn (fun i => (z i).val))=
      (decode r c z).map (fun T => matrixCode T.val) := by
  unfold originalCandidate
  rw [freeMatrix_code]
  unfold decode
  by_cases h : HasMargins (matrix z) r c
  · rw [ite_eq_left ((originalTableTest_code r c (matrix z)).mpr h),dite_eq_left h]
    rfl
  · rw [ite_eq_right (fun ht => h ((originalTableTest_code r c (matrix z)).mp ht)),dite_eq_right h]
    rfl

lemma candidates_code {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    originalCandidates (List.ofFn r,List.ofFn c)=
      List.ofFn (fun k : Index m n (∑ i,r i) =>
        (tableAt r c k).map (fun T => matrixCode T.val)) := by
  have hl : ((zeroGrid (0::List.ofFn r,0::List.ofFn c)).map
      (fun _ => false)).length=m*n := by
    simp only [zeroGrid,List.tail_cons,List.length_map,cellPairs,
      List.length_range,List.length_ofFn]
  unfold originalCandidates originalEnumerationData completionEnumerationData
  simp only [originalLayoutMargins,List.sum_cons,zero_add,List.sum_ofFn]
  rw [gridWords_finFunctions _ (∑ i,r i) (m*n) hl,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  exact candidate_code r c (finFunctionFinEquiv.symm k)

end
end ContingencyTables.OriginalTableBox

end OAI
