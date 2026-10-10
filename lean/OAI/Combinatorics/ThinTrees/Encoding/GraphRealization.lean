import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceChoice
import OAI.Combinatorics.ThinTrees.Arithmetic.UnaryArithmetic
import OAI.Combinatorics.ThinTrees.Continuation.Iteration

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

structure Graph where
  n : ℕ
  m : ℕ
  G : MultiGraph n m

abbrev graphDataCode := prodCode natCode (prodCode indicesCode indicesCode)
def Graph.data (a : Graph) :=
  (a.n,(List.ofFn (fun e => (a.G.left e).val),List.ofFn (fun e => (a.G.right e).val)))
def graphCode (a : Graph) : Word := graphDataCode a.data
abbrev view : Realizes graphCode graphDataCode Graph.data :=
  (identity graphDataCode).reindex graphCode Graph.data (fun _ => rfl)
private instance poly_view : PolyTime view := by
  unfold view
  apply poly_reindex

abbrev numVertices := view.then (first natCode (prodCode indicesCode indicesCode))
abbrev endpoints := view.then (second natCode (prodCode indicesCode indicesCode))
abbrev lefts := endpoints.then (first indicesCode indicesCode)
abbrev rights := endpoints.then (second indicesCode indicesCode)
def numEdges : Realizes graphCode natCode Graph.m :=
  (lefts.then (lengthList natCode)).congr (fun _a => List.length_ofFn)
instance poly_numEdges : PolyTime numEdges := by unfold numEdges;apply poly_congr

abbrev Edge := Σ a : Graph, Fin a.m
abbrev edgeCode := finFamilyCode graphCode Graph.m
abbrev edgeGraph : Realizes edgeCode graphCode (fun a : Edge => a.1) := familyFirst
abbrev edgeIndex : Realizes edgeCode natCode (fun a : Edge => a.2.val) := familyIndex

def edgeLeft : Realizes edgeCode natCode (fun a : Edge => (a.1.G.left a.2).val) :=
  ((edgeIndex.both (edgeGraph.then lefts)).then (getD natCode 0)).congr
    (fun a => getD_ofFn _ a.2 0)
def edgeRight : Realizes edgeCode natCode (fun a : Edge => (a.1.G.right a.2).val) :=
  ((edgeIndex.both (edgeGraph.then rights)).then (getD natCode 0)).congr
    (fun a => getD_ofFn _ a.2 0)
instance poly_edgeLeft : PolyTime edgeLeft := by unfold edgeLeft;apply poly_congr
instance poly_edgeRight : PolyTime edgeRight := by unfold edgeRight;apply poly_congr

def incidence : Realizes edgeCode vectorCode
    (fun a => List.ofFn (qdiff (a.1.G.left a.2) (a.1.G.right a.2))) :=
  let n := edgeGraph.then numVertices
  ((((n.both edgeLeft).then basisVector).both ((n.both edgeRight).then basisVector)).then
    vectorSub).congr (by
      intro a
      change zipDefault (fun p : ℚ×ℚ => p.1-p.2) 0 0
        (basisData (a.1.n,(a.1.G.left a.2).val),
          basisData (a.1.n,(a.1.G.right a.2).val)) = _
      simp only [basis_data]
      rw [vectorSub_data]
      rfl)
instance poly_incidence : PolyTime incidence := by unfold incidence;infer_instance

def incidenceRows : Realizes graphCode matrixCode
    (fun a => matrixData (fun e => qdiff (a.G.left e) (a.G.right e))) :=
  incidence.tabulateFin numEdges
instance poly_incidenceRows : PolyTime incidenceRows := by unfold incidenceRows;apply poly_tabulateFin

def laplacian : Realizes graphCode matrixCode (fun a => matrixData (qlap a.G)) :=
  let ones := ((constant graphCode ratCode 1).both numEdges).then (replicateList ratCode)
  let atoms := incidenceRows.then Normalization.Stack.outer.map
  (numVertices.both (ones.both atoms)).then weightedSum |>.congr (by
    intro a
    change weightedSumData (a.n,(List.replicate a.m (1:ℚ),
      (List.ofFn (fun e => List.ofFn (qdiff (a.G.left e) (a.G.right e)))).map _))=_
    rw [← List.ofFn_const (n:=a.m) (1:ℚ)]
    simp only [List.map_ofFn,Function.comp_def]
    change weightedSumData (a.n,(List.ofFn (fun _ : Fin a.m => (1:ℚ)),
      List.ofFn (fun e => matrixData (vecMulVec (qdiff (a.G.left e) (a.G.right e))
        (qdiff (a.G.left e) (a.G.right e))))))=_
    rw [weightedSum_data]
    simp only [one_smul,qlap])
instance poly_laplacian : PolyTime laplacian := by unfold laplacian;apply poly_congr

def constantMatrix : Realizes (prodCode natCode ratCode) matrixCode
    (fun p => matrixData (Matrix.of (fun (_ _ : Fin p.1) => p.2))) :=
  let n := first natCode ratCode
  let q := second natCode ratCode
  ((((q.both n).then (replicateList ratCode)).both n).then
    (replicateList vectorCode)).congr (fun p => by
      change List.replicate p.1 (List.replicate p.1 p.2)=
        List.ofFn (fun _ : Fin p.1 => List.ofFn (fun _ : Fin p.1 => p.2))
      simp)
instance poly_constantMatrix : PolyTime constantMatrix := by unfold constantMatrix;infer_instance

def projection : Realizes natCode matrixCode (fun n => matrixData (qproject n)) :=
  let inv := (constant natCode ratCode 1).div natToRat
  ((identityMatrix.both (((identity natCode).both inv).then constantMatrix)).then
    matrixSub).congr (by
      intro n
      rw [identityMatrix_data,matrixSub_data]
      simp only [one_div]
      rfl)
instance poly_projection : PolyTime projection := by unfold projection;infer_instance

def response : Realizes matrixObjectCode matrixCode (fun a => matrixData (qresponse a.2)) :=
  let P := matrixDim.then projection
  let A := matrixEntries
  let symm := (constant matrixObjectCode ratCode (1/2)).scaleMatrix
    ((A.both (A.then transposeMatrix)).then matrixAdd)
  ((P.both symm).then matrixMul).both P |>.then matrixMul |>.congr (by
    intro a
    rw [transpose_data]
    change matrixMulData (matrixMulData (matrixData (qproject a.1),
      matrixScaleData (1/2,matrixAddData (matrixData a.2,matrixData a.2.transpose))),
      matrixData (qproject a.1))=_
    unfold matrixAddData matrixScaleData
    rw [matrixAdd_data,matrixScale_data,matrixMul_data,matrixMul_data]
    rfl)
instance poly_response : PolyTime response := by unfold response;infer_instance

end AlgorithmicThinTrees.GraphStack

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix
open scoped BigOperators

lemma matIndex_val {n m : ℕ} (i j : Fin n) : (matIndex (m:=m) i j).val=j.val+n*i.val := rfl
lemma mulIndex_val {n m : ℕ} (i j k : Fin n) :
    (mulIndex (m:=m) (i,j,k)).val=n*n+(k.val+n*j.val+n*n*i.val) := rfl
lemma edgeIndex_val {n m : ℕ} (p : Fin 3) (e : Fin m) :
    (edgeIndex (n:=n) p e).val=n*n+(n*(n*n)+(e.val+m*p.val)) := rfl
lemma flowIndex_val {n m : ℕ} (p : Fin 2) (r : Fin n) (e : Fin m) :
    (flowIndex p r e).val=n*n+(n*(n*n)+(3*m+(e.val+m*r.val+n*m*p.val))) := rfl

abbrev dimsCode := prodCode natCode natCode
abbrev variablesCode := prodCode dimsCode vectorCode
abbrev variablesDims := first dimsCode vectorCode
abbrev variablesN := variablesDims.then (first natCode natCode)
abbrev variablesM := variablesDims.then (second natCode natCode)
abbrev variableValues := second dimsCode vectorCode

def dimensionProgram : Realizes dimsCode natCode (fun p => dimension p.1 p.2) :=
  let n := first natCode natCode
  let m := second natCode natCode
  (n.nmul n).nadd ((n.nmul (n.nmul n)).nadd
    (((constant dimsCode natCode 3).nmul m).nadd
      ((constant dimsCode natCode 2).nmul (n.nmul m))))
instance poly_dimensionProgram : PolyTime dimensionProgram := by
  unfold dimensionProgram Realizes.nadd
  apply poly_then

abbrev varEntryCode := prodCode (prodCode variablesCode natCode) natCode
abbrev varEntryContext := first (prodCode variablesCode natCode) natCode
abbrev varEntryVars := varEntryContext.then (first variablesCode natCode)
abbrev varEntryI := varEntryContext.then (second variablesCode natCode)
abbrev varEntryJ := second (prodCode variablesCode natCode) natCode

def rawEntry : Realizes varEntryCode ratCode
    (fun a => a.1.1.2.getD (a.2+a.1.1.1.1*a.1.2) 0) :=
  ((varEntryJ.nadd ((varEntryVars.then variablesN).nmul varEntryI)).both
    (varEntryVars.then variableValues)).then (getD ratCode 0)
instance poly_rawEntry : PolyTime rawEntry := by unfold rawEntry;infer_instance

def raw : Realizes variablesCode matrixCode
    (fun p => (List.range p.1.1).map (fun i =>
      (List.range p.1.1).map (fun j => p.2.getD (j+p.1.1*i) 0))) :=
  (((identity variablesCode).both variablesN).both variablesN).then rawEntry.matrixTabulate
instance poly_raw : PolyTime raw := by unfold raw;infer_instance

lemma raw_data {n m : ℕ} (v : Fin (dimension n m) → ℚ) :
    (List.range n).map (fun i => (List.range n).map
      (fun j => (List.ofFn v).getD (j+n*i) 0))=matrixData (rawMatrix v) := by
  simp only [range_map_fin,matrixData]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [←matIndex_val i j,getD_ofFn]
  rfl

def edgeVariable (p : ℕ) : Realizes (prodCode variablesCode natCode) ratCode
    (fun a => a.1.2.getD (a.1.1.1*a.1.1.1+(a.1.1.1*(a.1.1.1*a.1.1.1)+
      (a.2+a.1.1.2*p))) 0) :=
  let c := first variablesCode natCode
  let n := c.then variablesN
  let m := c.then variablesM
  let e := second variablesCode natCode
  let idx := (n.nmul n).nadd ((n.nmul (n.nmul n)).nadd
    (e.nadd (m.nmul (constant _ natCode p))))
  (idx.both (c.then variableValues)).then (getD ratCode 0)
instance poly_edgeVariable (p : ℕ) : PolyTime (edgeVariable p) := by unfold edgeVariable;infer_instance

lemma edgeVariable_data {n m : ℕ} (v : Fin (dimension n m) → ℚ) (p : Fin 3) (e : Fin m) :
    (List.ofFn v).getD (n*n+(n*(n*n)+(e.val+m*p.val))) 0=v (edgeIndex p e) := by
  rw [←edgeIndex_val p e,getD_ofFn]

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
