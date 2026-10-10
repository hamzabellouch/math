import OAI.Combinatorics.ContingencyTables.Rooted.RootedForestCatalog
import OAI.Combinatorics.ContingencyTables.Rooted.RootedComponentCode

namespace OAI

/-! # Computing the root-demand input from the actual cell arrays

The two natural entries at a vertex encode its signed small-cell
discrepancy. They are formed by rectangular scans and then passed to the
component/root program.
-/

namespace ContingencyTables.RootedDemandProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms SignedPairProgram
open FiniteGraphRootProgram
open scoped BigOperators Classical

abbrev Input := RootedForestCatalog.Data×(MatrixCode×(MatrixCode×MatrixCode))
abbrev TermInput := (Input×ℕ)×(ℕ×ℕ)

def values (z : TermInput) : (ℕ×ℕ)×(ℕ×ℕ) :=
  RootedCellDataProgram.values (((z.1.1.1.2,z.1.1.2.1),z.1.1.2.2),z.2)
def valuesRealizer : Realizer values :=
  composition (f := fun z : TermInput =>
    (((z.1.1.1.2,z.1.1.2.1),z.1.1.2.2),z.2)) (g := RootedCellDataProgram.values) (pair
    (pair (pair (composition (composition (composition first first) first) second)
      (composition (composition (composition first first) second) first))
      (composition (composition (composition first first) second) second))
    second) RootedCellDataProgram.valuesRealizer
lemma polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair
      (polynomial_pair
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first))
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
    polynomial_second) RootedCellDataProgram.polynomial_values

def retainedTest (z : TermInput) : Bool :=
  !RootedForestCatalog.largeTest (z.1.1.1,z.2)
def retainedTestRealizer : Realizer retainedTest :=
  composition (composition (pair (composition (composition first first) first) second)
    RootedForestCatalog.largeTestRealizer) boolNot
lemma polynomial_retainedTest : PolynomialTime retainedTestRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) RootedForestCatalog.polynomial_largeTest) polynomial_boolNot

def rowTest (z : TermInput) : Bool := decide (z.1.2=z.2.1)
def rowTestRealizer : Realizer rowTest :=
  composition (pair (composition first second) (composition second first)) natEqual
lemma polynomial_rowTest : PolynomialTime rowTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual

def columnTest (z : TermInput) : Bool :=
  decide (z.1.2=z.1.1.1.1.2.1.length+z.2.2)
def columnTestRealizer : Realizer columnTest :=
  composition (pair (composition first second)
    (composition (pair
      (composition (composition (composition (composition (composition (composition first first)
        first) first) second) first) listLength) (composition second second)) add)) natEqual
lemma polynomial_columnTest : PolynomialTime columnTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first
          polynomial_first) polynomial_first) polynomial_first) polynomial_second) polynomial_first)
        polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)) polynomial_natEqual

def rowPair (z : TermInput) : Signed := ((values z).1.2,(values z).2.1)
def rowPairRealizer : Realizer rowPair :=
  pair
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.1.2)
      valuesRealizer (composition first second))
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.2.1)
      valuesRealizer (composition second first))
lemma polynomial_rowPair : PolynomialTime rowPairRealizer :=
  polynomial_pair
    (polynomial_composition polynomial_values (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_values (polynomial_composition polynomial_second polynomial_first))

def columnPair (z : TermInput) : Signed := ((values z).2.2,(values z).1.2)
def columnPairRealizer : Realizer columnPair :=
  pair
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.2.2)
      valuesRealizer (composition second second))
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.1.2)
      valuesRealizer (composition first second))
lemma polynomial_columnPair : PolynomialTime columnPairRealizer :=
  polynomial_pair
    (polynomial_composition polynomial_values (polynomial_composition polynomial_second polynomial_second))
    (polynomial_composition polynomial_values (polynomial_composition polynomial_first polynomial_second))

def term (z : TermInput) : Signed :=
  if retainedTest z then
    plus ((if rowTest z then rowPair z else (0,0)),
      (if columnTest z then columnPair z else (0,0)))
  else (0,0)
def termRealizer : Realizer term :=
  choose retainedTestRealizer
    (composition (pair (choose rowTestRealizer rowPairRealizer (constant (0,0)))
      (choose columnTestRealizer columnPairRealizer (constant (0,0)))) plusRealizer)
    (constant (0,0))
lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_choose polynomial_retainedTest
    (polynomial_composition (polynomial_pair
      (polynomial_choose polynomial_rowTest polynomial_rowPair (polynomial_constant (0,0)))
      (polynomial_choose polynomial_columnTest polynomial_columnPair (polynomial_constant (0,0))))
      polynomial_plus) (polynomial_constant (0,0))

def demand (z : Input×ℕ) : Signed :=
  sum ((cellPairs z.1.1.1.2).map (fun a => term (z,a)))
def demandRealizer : Realizer demand :=
  composition (composition (pair identity
    (composition (composition (composition (composition first first) first) second)
      cellPairsRealizer)) (mapWith termRealizer)) sumRealizer
lemma polynomial_demand : PolynomialTime demandRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_cellPairs)) (polynomial_mapWith polynomial_term)) polynomial_sum

def vertexCount (z : Input) : ℕ := z.1.1.2.1.length+z.1.1.2.2.length
def vertexCountRealizer : Realizer vertexCount :=
  composition (pair
    (composition (composition (composition (composition first first) second) first) listLength)
    (composition (composition (composition (composition first first) second) second) listLength)) add
lemma polynomial_vertexCount : PolynomialTime vertexCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
      polynomial_listLength)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
      polynomial_listLength)) polynomial_add

def vertices (z : Input) : List ℕ := List.range (vertexCount z)
def verticesRealizer : Realizer vertices := composition vertexCountRealizer range
lemma polynomial_vertices : PolynomialTime verticesRealizer := by
  apply polynomial_boundedRange polynomial_vertexCount (2*Polynomial.X)
  intro z
  have h₁ : z.1.1.2.1.length≤weight z := (list_length_le_weight _).trans
    ((weight_fst _).trans ((weight_snd _).trans ((weight_fst _).trans (weight_fst _))))
  have h₂ : z.1.1.2.2.length≤weight z := (list_length_le_weight _).trans
    ((weight_snd _).trans ((weight_snd _).trans ((weight_fst _).trans (weight_fst _))))
  simp only [vertexCount,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

def demandList (z : Input) : List Signed := (vertices z).map (fun v => demand (z,v))
def demandListRealizer : Realizer demandList :=
  composition (pair identity verticesRealizer) (mapWith demandRealizer)
lemma polynomial_demandList : PolynomialTime demandListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_vertices)
    (polynomial_mapWith polynomial_demand)

def rootCount (z : Input) : ℕ := RootedComponentCode.count (z.1.1.1.1,demandList z)
def rootCountRealizer : Realizer rootCount :=
  composition (pair (composition (composition (composition first first) first) first)
    demandListRealizer) RootedComponentCode.countRealizer
theorem polynomial_rootCount : PolynomialTime rootCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first
      polynomial_first) polynomial_first) polynomial_first) polynomial_demandList)
    RootedComponentCode.polynomial_count

open CompanionFactorialApplication RootedCompletion

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) : Input :=
  (RootedForestCatalog.data A,
    (matrixCode (fun i j => (A.X i j).toNat),(matrixCode x,matrixCode q)))

lemma values_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : ℕ) (i : Fin m) (j : Fin n) :
    values ((data A x q,v),(i.val,j.val))=
      ((A.b i j,(A.X i j).toNat),(x i j,q i j)) := by
  simp only [values,data,RootedForestCatalog.data,RootedCellDataProgram.values,matrixEntry_code]

lemma retainedTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : ℕ) (i : Fin m) (j : Fin n) :
    retainedTest ((data A x q,v),(i.val,j.val))=A.small i j := by
  unfold retainedTest RootedForestCatalog.largeTest
  simp only [data,RootedForestCatalog.data,matrixEntry_code]
  cases hs : A.small i j with
  | false => simp [(A.hlarge _ _ hs).1]
  | true => simp [Nat.not_le.mpr (A.hsmall _ _ hs)]

lemma rowTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (i : Fin m) (j : Fin n) :
    rowTest ((data A x q,(finSumFinEquiv v).val),(i.val,j.val))=decide (v=Sum.inl i) := by
  cases v with
  | inl a =>
    simp only [rowTest,finSumFinEquiv_apply_left,Fin.val_castAdd,Sum.inl.injEq,Fin.ext_iff]
    rfl
  | inr b =>
    have hi : i.val < m := i.isLt
    have hne : m+b.val≠i.val := by omega
    simp only [rowTest,finSumFinEquiv_apply_right,Fin.val_natAdd,hne,
      Sum.inr_ne_inl,decide_false]

lemma columnTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (i : Fin m) (j : Fin n) :
    columnTest ((data A x q,(finSumFinEquiv v).val),(i.val,j.val))=decide (v=Sum.inr j) := by
  apply Bool.eq_iff_iff.mpr
  cases v with
  | inl a =>
    simp only [columnTest,data,RootedForestCatalog.data,List.length_ofFn,
      finSumFinEquiv_apply_left,Fin.val_castAdd,decide_eq_true_eq,Sum.inl_ne_inr,iff_false]
    have ha := a.isLt
    omega
  | inr b =>
    simp only [columnTest,data,RootedForestCatalog.data,List.length_ofFn,
      finSumFinEquiv_apply_right,Fin.val_natAdd,decide_eq_true_eq,Sum.inr.injEq,
      Nat.add_left_cancel_iff,Fin.ext_iff]

noncomputable def contribution {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (a : Fin m×Fin n) : ℤ :=
  if A.small a.1 a.2 then
    (if v=Sum.inl a.1 then A.X a.1 a.2-(x a.1 a.2:ℤ) else 0)+
      (if v=Sum.inr a.2 then (q a.1 a.2:ℤ)-A.X a.1 a.2 else 0)
  else 0

lemma term_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (i : Fin m) (j : Fin n) :
    value (term ((data A x q,(finSumFinEquiv v).val),(i.val,j.val)))=
      contribution A x q v (i,j) := by
  rw [term,retainedTest_data,rowTest_data,columnTest_data]
  by_cases hs : A.small i j=true <;> by_cases hr : v=Sum.inl i <;>
    by_cases hc : v=Sum.inr j
  all_goals simp [hs,hr,hc,rowPair,columnPair,values_data,
    contribution,value,SignedPairProgram.plus,Int.toNat_of_nonneg (A.hX i j).1]

lemma contribution_sum {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) :
    (∑ a : Fin m×Fin n,contribution A x q v a)=
      ForestRootPenalty.smallDemand A.small A.X
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) v := by
  cases v with
  | inl i =>
    have ht (k : Fin m) (j : Fin n) : contribution A x q (.inl i) (k,j)=
        if k=i then (if A.small i j then A.X i j-(x i j:ℤ) else 0) else 0 := by
      by_cases hk : k=i
      · subst k; simp [contribution]
      · simp [contribution,hk,Ne.symm hk]
    simp only [Fintype.sum_prod_type,ht]
    simp [ForestRootPenalty.smallDemand]
  | inr j =>
    have ht (i : Fin m) (k : Fin n) : contribution A x q (.inr j) (i,k)=
        if k=j then (if A.small i j then (q i j:ℤ)-A.X i j else 0) else 0 := by
      by_cases hk : k=j
      · subst k; simp [contribution]
      · simp [contribution,hk,Ne.symm hk]
    simp only [Fintype.sum_prod_type,ht]
    simp [ForestRootPenalty.smallDemand]

lemma demand_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) :
    value (demand (data A x q,(finSumFinEquiv v).val))=
      ForestRootPenalty.smallDemand A.small A.X
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) v := by
  have hc : cellPairs (data A x q).1.1.2=
      List.ofFn (fun a : Fin (m*n) =>
        (((finProdFinEquiv : Fin m×Fin n≃Fin (m*n)).symm a).1.val,
          ((finProdFinEquiv : Fin m×Fin n≃Fin (m*n)).symm a).2.val)) :=
    DensePrograms.cellPairs_ofFn _ _
  rw [demand,value_sum,hc]
  simp only [List.map_ofFn,Function.comp_apply,List.sum_ofFn,term_data]
  calc
    _=∑ a : Fin m×Fin n,contribution A x q v a :=
      Fintype.sum_equiv (finProdFinEquiv : Fin m×Fin n≃Fin (m*n)).symm _ _ (fun _ => rfl)
    _=_ := contribution_sum A x q v

lemma demandList_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) :
    demandList (data A x q)=List.ofFn (fun i : Fin (m+n) => demand (data A x q,i.val)) := by
  apply List.ext_getElem
  · simp only [demandList,vertices,vertexCount,data,RootedForestCatalog.data,List.length_map,
      List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [demandList,vertices,vertexCount,data,RootedForestCatalog.data,List.length_ofFn,
      List.getElem_map,List.getElem_range,List.getElem_ofFn]

/-- The actual binary root program has exactly the selected-root penalty
value; no signed-demand representation assumption is supplied. -/
theorem rootCount_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) :
    rootCount (data A x q)=RootedPenaltyProgram.rootCount A (rowColumn A.T)
      (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) := by
  rw [rootCount,demandList_data]
  change RootedComponentCode.count
    (graphCode (A.T.comap finSumFinEquiv.symm),List.ofFn (fun i : Fin (m+n) =>
      ((demand (data A x q,i.val)).1,(demand (data A x q,i.val)).2)))=_
  rw [RootedComponentCode.count,RootedComponentCode.labels_graph]
  have ht := RootedComponentProgram.total_records_rootCount A (rowColumn A.T)
    (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) finSumFinEquiv.symm
    (fun i => (demand (data A x q,i.val)).1) (fun i => (demand (data A x q,i.val)).2)
    (fun i => by
      have h := demand_data A x q (finSumFinEquiv.symm i)
      simpa only [Equiv.apply_symm_apply,value] using h)
  simpa only [rowColumn_root,Equiv.apply_symm_apply,Equiv.symm_apply_apply] using ht

end ContingencyTables.RootedDemandProgram

end OAI
