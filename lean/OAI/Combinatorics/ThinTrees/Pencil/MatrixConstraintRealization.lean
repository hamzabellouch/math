import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.ArraySums
import OAI.Combinatorics.ThinTrees.Pencil.PointPrograms
import OAI.Combinatorics.ThinTrees.Pencil.RationalAffineEval

namespace OAI

/-! Matrix constraint realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {I : α → Type*} [∀a,Fintype (I a)]
def Realizes.sumIndexedMatrices {n d : α → ℕ} {e : (a : α) → I a ≃ Fin (n a)}
    {A : (a : α) → I a → Matrix (Fin (d a)) (Fin (d a)) ℚ}
    (r : Realizes (indexedCode ea e) matrixCode (fun a => matrixData (A a.1 a.2)))
    (rn : Realizes ea natCode n) (rd : Realizes ea natCode d) :
    Realizes ea matrixCode (fun a => matrixData (∑i,A a i)) :=
  ((rd.both (r.tabulateIndexed rn)).then matrixSum).congr (by
    intro a
    rw [matrixSum_data]
    exact congrArg matrixData ((e a).symm.sum_comp (A a)))
instance poly_sumIndexedMatrices {n d : α → ℕ} {e : (a : α) → I a ≃ Fin (n a)}
    {A : (a : α) → I a → Matrix (Fin (d a)) (Fin (d a)) ℚ}
    (r : Realizes (indexedCode ea e) matrixCode (fun a => matrixData (A a.1 a.2)))
    (rn : Realizes ea natCode n) (rd : Realizes ea natCode d)
    [PolyTime r] [PolyTime rn] [PolyTime rd] : PolyTime (r.sumIndexedMatrices rn rd) := by
  unfold Realizes.sumIndexedMatrices;infer_instance
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

lemma rat_matrixForm {n m : ℕ} (v : Fin (dimension n m) → ℚ) (i j : Fin n) :
    Affine.rat v (matrixForm i j)=qresponse (rawMatrix v) i j := by
  simp only [matrixForm,Affine.rat_sum,Affine.rat_smul,Affine.rat_add,Affine.rat_coord]
  simp only [qresponse,Matrix.mul_apply,Matrix.smul_apply,Matrix.add_apply,
    Matrix.transpose_apply,rawMatrix,smul_eq_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

namespace Stack

def triangleAt {n : ℕ} (t : Triple n) : Matrix (Fin n) (Fin n) ℚ :=
  vecMulVec (qdiff t.1 t.2.1) (qdiff t.1 t.2.1)+
    vecMulVec (qdiff t.2.1 t.2.2) (qdiff t.2.1 t.2.2)-
    vecMulVec (qdiff t.1 t.2.2) (qdiff t.1 t.2.2)

def triangleMatrixProgram : Realizes tripleCode matrixCode (fun p => matrixData (triangleAt p.2)) :=
  let n := triplePoint.then pointN
  let ij := (differenceVector n (fun p => p.2.1) (fun p => p.2.2.1) tripleI tripleJ).then
    Normalization.Stack.outer
  let jk := (differenceVector n (fun p => p.2.2.1) (fun p => p.2.2.2) tripleJ tripleK).then
    Normalization.Stack.outer
  let ik := (differenceVector n (fun p => p.2.1) (fun p => p.2.2.2) tripleI tripleK).then
    Normalization.Stack.outer
  (((ij.both jk).then matrixAdd).both ik).then matrixSub |>.congr (by
    intro a
    dsimp only [KS.W13.ExpressionMachine.BinaryOp.eval]
    rw [Normalization.Stack.outer_data,Normalization.Stack.outer_data,Normalization.Stack.outer_data,
      matrixAdd_data,matrixSub_data]
    rfl)
instance poly_triangleMatrixProgram : PolyTime triangleMatrixProgram := by
  have hi : PolyTime tripleI := by infer_instance
  have hj : PolyTime tripleJ := by infer_instance
  have hk : PolyTime tripleK := by infer_instance
  have hn : PolyTime (triplePoint.then pointN) := by infer_instance
  have hij : PolyTime ((differenceVector (triplePoint.then pointN)
      (fun p => p.2.1) (fun p => p.2.2.1) tripleI tripleJ).then Normalization.Stack.outer) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact @poly_differenceVector _ _ _ _ _ _ _ _ hn hi hj
    · infer_instance
  have hjk : PolyTime ((differenceVector (triplePoint.then pointN)
      (fun p => p.2.2.1) (fun p => p.2.2.2) tripleJ tripleK).then Normalization.Stack.outer) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact @poly_differenceVector _ _ _ _ _ _ _ _ hn hj hk
    · infer_instance
  have hik : PolyTime ((differenceVector (triplePoint.then pointN)
      (fun p => p.2.1) (fun p => p.2.2.2) tripleI tripleK).then Normalization.Stack.outer) := by
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · exact @poly_differenceVector _ _ _ _ _ _ _ _ hn hi hk
    · infer_instance
  unfold triangleMatrixProgram
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  apply poly_then

def weightedTriangle (a : Point) (t : Triple a.p.graph.n) : Matrix (Fin a.p.graph.n) (Fin a.p.graph.n) ℚ :=
  if t.1≠t.2.1 ∧ t.2.1≠t.2.2 ∧ t.1≠t.2.2 then a.v (mulIndex t) • triangleAt t else 0

def weightedTriangleProgram : Realizes tripleCode matrixCode (fun a => matrixData (weightedTriangle a.1 a.2)) :=
  let val := tripleCoordinate.scaleMatrix triangleMatrixProgram
  (tripleDistinct.ite val (triplePoint.then pointN |>.then zeroMatrix)).congr (by
    intro a
    simp only [weightedTriangle,decide_eq_true_eq]
    split_ifs
    · exact matrixScale_data _ _
    · rfl)
instance poly_weightedTriangleProgram : PolyTime weightedTriangleProgram := by
  unfold weightedTriangleProgram;infer_instance

lemma weightedTriangle_sum (a : Point) :
    ∑t,weightedTriangle a t = ∑t : DistinctTriple a.p.graph.n,a.v (mulIndex t.val) • qtriangle t := by
  classical
  let P (t : Triple a.p.graph.n) := t.1≠t.2.1 ∧ t.2.1≠t.2.2 ∧ t.1≠t.2.2
  rw [←Fintype.sum_subtype_add_sum_subtype P (weightedTriangle a)]
  have hz : ∑ t : {t // ¬ P t}, weightedTriangle a t.val = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact ite_eq_right t.property
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  unfold weightedTriangle
  rw [ite_eq_left t.property]
  rfl

def triangleSum : Realizes pointCode matrixCode (fun a =>
    matrixData (∑t : DistinctTriple a.p.graph.n,a.v (mulIndex t.val) • qtriangle t)) :=
  (weightedTriangleProgram.sumIndexedMatrices (A:=weightedTriangle) (pointN.nmul (pointN.nmul pointN)) pointN).congr (by
    intro a
    rw [weightedTriangle_sum])
instance poly_triangleSum : PolyTime triangleSum := by unfold triangleSum;infer_instance

def lowerMatrix : Realizes pointCode matrixCode (fun a => matrixData ((lowerForm a.p.graph.G).map (Affine.rat a.v))) :=
  ((responsePoint.both lapPoint).then matrixSub).congr (by
    intro a
    rw [matrixSub_data]
    congr 1
    ext i j
    simp [lowerForm,rat_matrixForm,Matrix.sub_apply])
instance poly_lowerMatrix : PolyTime lowerMatrix := by unfold lowerMatrix;infer_instance

def upperMatrix : Realizes pointCode matrixCode (fun a => matrixData ((upperForm a.p.graph.G).map (Affine.rat a.v))) :=
  (((((constant pointCode ratCode 3).scaleMatrix lapPoint).both responsePoint).then matrixSub).both triangleSum).then
    matrixSub |>.congr (by
      intro a
      rw [matrixScale_data,matrixSub_data,matrixSub_data]
      congr 1
      ext i j
      simp only [Matrix.map_apply,upperForm,Affine.rat_sub,Affine.rat_cst,Affine.rat_sum,
        Affine.rat_smul,Affine.rat_coord,rat_matrixForm,Matrix.sub_apply,Matrix.smul_apply,
        smul_eq_mul,Matrix.sum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      ring)
instance poly_upperMatrix : PolyTime upperMatrix := by unfold upperMatrix;infer_instance

def edgeMatrix : Realizes (indexedCode pointCode eEquiv) matrixCode (fun a =>
    matrixData ((matrixBlocks a.1.p.graph.G a.1.p.s a.1.p.u (.inr a.2)).map (Affine.rat a.1.v))) :=
  let p := indexedFirst (ea:=pointCode) eEquiv
  let e := indexedIndex (ea:=pointCode) eEquiv
  let isActive := (constant _ ratCode 0).lt (storedU p (fun a => a.2) e)
  let atom := ((graphEdge p (fun a => a.2) e).then GraphStack.incidence).then Normalization.Stack.outer
  let factor := ((constant _ ratCode 6).mul (p.then pointS)).mul (edgeCoord 0 p (fun a => a.2) e)
  let response := ((p.then responsePoint).both (factor.scaleMatrix atom)).then matrixSub
  (isActive.ite response (p.then pointN |>.then zeroMatrix)).congr (by
    intro a
    simp only [decide_eq_true_eq,matrixBlocks]
    split_ifs
    · rw [Normalization.Stack.outer_data,matrixScale_data,matrixSub_data]
      congr 1
      ext i j
      simp [edgeForm,rat_matrixForm,Matrix.sub_apply,smul_eq_mul,Matrix.vecMulVec_apply]
      ring
    · congr 1
      ext i j
      simp)
instance poly_edgeMatrix : PolyTime edgeMatrix := by
  have hp : PolyTime (indexedFirst (ea:=pointCode) eEquiv) := by infer_instance
  have he : PolyTime (indexedIndex (ea:=pointCode) eEquiv) := by infer_instance
  unfold edgeMatrix
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_ite _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · refine @poly_lt _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · exact @poly_storedU _ _ _ _ _ _ hp he
  · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply poly_then
      · refine @poly_scaleMatrix _ _ _ _ _ _ ?_ ?_
        · refine @poly_mul _ _ _ _ _ _ ?_ ?_
          · refine @poly_mul _ _ _ _ _ _ ?_ ?_
            · infer_instance
            · refine @poly_then _ _ _ _ _ _ _ _ _ _ hp ?_
              unfold pointS paramsS
              refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
              · infer_instance
              · apply poly_paramsField
          · exact @poly_edgeCoord _ _ _ _ _ _ _ hp he
        · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
          · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
            · exact @poly_graphEdge _ _ _ _ _ _ hp he
            · infer_instance
          · infer_instance
    · infer_instance
  · infer_instance

abbrev matrixBlockEquiv := sumEquiv (fun _ : Point => Equiv.refl (Fin 2)) eEquiv

def specialMatrix : Realizes (indexedCode pointCode (fun _ : Point => Equiv.refl (Fin 2))) matrixCode
    (fun a => matrixData ((matrixBlocks a.1.p.graph.G a.1.p.s a.1.p.u (.inl a.2)).map (Affine.rat a.1.v))) :=
  let p := indexedFirst (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 2))
  let i := indexedIndex (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 2))
  ((i.finEq (constant _ natCode (0 : Fin 2).val)).ite (p.then lowerMatrix) (p.then upperMatrix)).congr (by
    intro a
    change (if decide (a.2 = 0) = true then
      matrixData ((lowerForm a.1.p.graph.G).map (Affine.rat a.1.v)) else
      matrixData ((upperForm a.1.p.graph.G).map (Affine.rat a.1.v))) =
      matrixData ((if a.2 = 0 then lowerForm a.1.p.graph.G else
        upperForm a.1.p.graph.G).map (Affine.rat a.1.v))
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl)
instance poly_specialMatrix : PolyTime specialMatrix := by unfold specialMatrix;infer_instance

def matrixConstraints : Realizes (indexedCode pointCode matrixBlockEquiv) matrixCode
    (fun a => matrixData ((matrixBlocks a.1.p.graph.G a.1.p.s a.1.p.u a.2).map (Affine.rat a.1.v))) :=
  (specialMatrix.sumCases edgeMatrix (constant pointCode natCode 2)).congr (by
    rintro ⟨a,b|e⟩ <;> rfl)
instance poly_matrixConstraints : PolyTime matrixConstraints := by unfold matrixConstraints;infer_instance
end Stack
end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
