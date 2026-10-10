import Mathlib
import OAI.Combinatorics.ThinTrees.Pencil.BlockAssembly
import OAI.Combinatorics.ThinTrees.Pencil.MatrixConstraintRealization
import OAI.Combinatorics.ThinTrees.Pencil.ScalarConstraintRealization

namespace OAI

/-! Pencil realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack

abbrev matrixCount := (constant pointCode natCode 2).nadd pointM
abbrev scalarCount := (pointN.nmul (pointN.nmul pointN)).nadd
  (((constant pointCode natCode 7).nmul pointM).nadd
    (((constant pointCode natCode 3).nmul (pointN.nmul pointM)).nadd
      ((pointN.nmul pointN).nadd (constant pointCode natCode 1))))

instance poly_matrixCount : PolyTime matrixCount := by unfold matrixCount;infer_instance
instance poly_scalarCount : PolyTime scalarCount := by unfold scalarCount;infer_instance

lemma rowIndex_blocks (a : Point) :
    blockRowEquiv (n:=a.p.graph.n) (matrixBlockEquiv a) (scalarEquiv a)=
      rowIndex a.p.graph.n a.p.graph.m := by
  apply Equiv.ext
  intro i
  rcases i with ⟨i,b|e⟩ | (t | (e | (f | (v | u)))) <;> rfl

lemma affineMatrix_rat (a : Point) :
    (affineMatrix a.p.graph.G a.p.s a.p.κ a.p.t a.p.q a.p.ε a.p.u).map (Affine.rat a.v)=
      (Matrix.fromBlocks
        (Matrix.blockDiagonal (fun b => (matrixBlocks a.p.graph.G a.p.s a.p.u b).map (Affine.rat a.v)))
        0 0 (Matrix.diagonal (scalarValue a))).submatrix
          (rowIndex a.p.graph.n a.p.graph.m).symm (rowIndex a.p.graph.n a.p.graph.m).symm := by
  ext i j
  obtain ⟨i,rfl⟩ := (rowIndex a.p.graph.n a.p.graph.m).surjective i
  obtain ⟨j,rfl⟩ := (rowIndex a.p.graph.n a.p.graph.m).surjective j
  simp only [affineMatrix,Matrix.map_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rcases i with ⟨i,b⟩ | s <;> rcases j with ⟨j,c⟩ | t
  · simp only [Matrix.fromBlocks_apply₁₁,Matrix.blockDiagonal,Matrix.of_apply]
    split_ifs <;> simp
  · simp
  · simp
  · by_cases h : s=t <;> simp [scalarValue,h]

def affinePoint : Realizes pointCode matrixCode (fun a =>
    matrixData ((affineMatrix a.p.graph.G a.p.s a.p.κ a.p.t a.p.q a.p.ε a.p.u).map (Affine.rat a.v))) :=
  ((pointN.both ((matrixConstraints.tabulateIndexed matrixCount).both
    (scalarConstraints.tabulateIndexed scalarCount))).then stitchProgram).congr (by
      intro a
      have h := stitch_data (n:=a.p.graph.n) (matrixBlockEquiv a) (scalarEquiv a)
        (fun b => (matrixBlocks a.p.graph.G a.p.s a.p.u b).map (Affine.rat a.v)) (scalarValue a)
      rw [rowIndex_blocks] at h
      exact h.trans (congrArg matrixData (affineMatrix_rat a)).symm)
instance poly_affinePoint : PolyTime affinePoint := by
  have : PolyTime pointN := by infer_instance
  unfold affinePoint;infer_instance

def pencilEval := pointParser.then affinePoint
instance poly_pencilEval : PolyTime pencilEval := by unfold pencilEval;infer_instance

lemma pencilEval_data (p : Params) (v : Fin (dimension p.graph.n p.graph.m) → ℚ) :
    matrixData ((affineMatrix (parsePoint (p,List.ofFn v)).p.graph.G
      (parsePoint (p,List.ofFn v)).p.s (parsePoint (p,List.ofFn v)).p.κ
      (parsePoint (p,List.ofFn v)).p.t (parsePoint (p,List.ofFn v)).p.q
      (parsePoint (p,List.ofFn v)).p.ε (parsePoint (p,List.ofFn v)).p.u).map
        (Affine.rat (parsePoint (p,List.ofFn v)).v)) = matrixData (p.pencil.eval v) := by
  rw [parsePoint_ofFn]
  unfold Params.pencil continuationPencil
  rw [pencil_eval]

def buildPencil : Realizes paramsCode pencilCode (fun p => pencilData p.pencil) :=
  (((identity paramsCode).both paramsDim).then pencilEval.pencilFromEval).congr (by
    intro p
    apply pencilFromEval_data
    exact pencilEval_data p)
instance poly_buildPencil : PolyTime buildPencil := by unfold buildPencil;infer_instance
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
