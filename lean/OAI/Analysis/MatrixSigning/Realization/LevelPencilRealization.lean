import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.BlockScalar
import OAI.Analysis.MatrixSigning.Realization.PencilArrayRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α : Type*}
def singletonList (ea : α → Word) : Realizes ea (listCode ea) (fun x => [x]) :=
  ((identity ea).both (constant ea (listCode ea) [])).then (consList ea)

def replicateList (ea : α → Word) :
    Realizes (prodCode ea natCode) (listCode ea) (fun p => List.replicate p.2 p.1) :=
  (first ea natCode).tabulate.congr (by intro p;simp)

def blockScalarData (p : MatrixData×ℚ) : MatrixData :=
  p.1.map (fun row => row++[0]) ++ [List.replicate p.1.length 0++[p.2]]

def blockScalar : Realizes (prodCode matrixCode ratCode) matrixCode blockScalarData :=
  let M := first matrixCode ratCode
  let q := second matrixCode ratCode
  let top := M.then (((identity vectorCode).both (constant vectorCode vectorCode [0])).then
    (appendList ratCode)).map
  let zeros := ((constant (prodCode matrixCode ratCode) ratCode 0).both
    (M.then (lengthList vectorCode))).then (replicateList ratCode)
  let bottom := (zeros.both (q.then (singletonList ratCode))).then (appendList ratCode)
  (top.both (bottom.then (singletonList vectorCode))).then (appendList vectorCode)

lemma blockScalar_data {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ) (q : ℚ) :
    blockScalarData (matrixData M,q)=matrixData (RationalSDP.blockScalar M q) := by
  unfold blockScalarData matrixData
  simp only [List.map_ofFn,Function.comp_def,List.length_ofFn]
  rw [List.ofFn_succ_last]
  congr 1
  · apply congrArg List.ofFn
    funext i
    rw [List.ofFn_succ_last]
    simp [RationalSDP.blockScalar,Matrix.submatrix,finSumFinEquiv_symm_apply_castSucc]
  · congr 1
    rw [List.ofFn_succ_last]
    simp only [RationalSDP.blockScalar,Matrix.submatrix,Matrix.of_apply,finSumFinEquiv_symm_last,
      finSumFinEquiv_symm_apply_castSucc,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply,List.ofFn_const]

abbrev levelInputCode := prodCode pencilCode (prodCode vectorCode ratCode)
def withLevelData (p : PencilData×(List ℚ×ℚ)) : PencilData :=
  (blockScalarData (p.1.1,p.2.2),
    zipDefault (fun z : MatrixData×ℚ => blockScalarData (z.1,-z.2)) [] 0 (p.1.2,p.2.1))
def withLevel : Realizes levelInputCode pencilCode withLevelData :=
  let B := first pencilCode (prodCode vectorCode ratCode)
  let f := (second pencilCode (prodCode vectorCode ratCode)).then (first vectorCode ratCode)
  let q := (second pencilCode (prodCode vectorCode ratCode)).then (second vectorCode ratCode)
  let C := B.then (first matrixCode (listCode matrixCode))
  let coeff := B.then (second matrixCode (listCode matrixCode))
  let one := ((first matrixCode ratCode).both (second matrixCode ratCode).neg).then blockScalar
  ((C.both q).then blockScalar).both ((coeff.both f).then (one.zipWith [] 0))

lemma withLevel_data {n m : ℕ} (B : RationalSDP.Pencil n m) (f : Fin n → ℚ) (q : ℚ) :
    withLevelData (pencilData B,(List.ofFn f,q))=pencilData (B.withLevel f q) := by
  unfold withLevelData pencilData
  rw [zipDefault_ofFn,blockScalar_data]
  simp only [blockScalar_data,RationalSDP.Pencil.withLevel]

end CurrentKS.Realization

end OAI
