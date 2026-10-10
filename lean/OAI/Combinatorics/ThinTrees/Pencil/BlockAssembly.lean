import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.UnaryArithmetic
import OAI.Combinatorics.ThinTrees.Continuation.Interior

namespace OAI

/-! Block assembly. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix KS.W23

abbrev BlocksData := ℕ × (List MatrixData × List ℚ)
abbrev blocksCode := prodCode natCode (prodCode (listCode matrixCode) vectorCode)
def stitchEntry (p : (BlocksData×ℕ)×ℕ) : ℚ :=
  let k := p.1.1.2.1.length
  let cut := p.1.1.1*k
  if p.1.2<cut then
    if p.2<cut then
      if p.1.2%k=p.2%k then
        (((p.1.1.2.1.getD (p.1.2%k) []).getD (p.1.2/k) []).getD (p.2/k) 0)
      else 0
    else 0
  else if p.1.2=p.2 then p.1.1.2.2.getD (p.1.2-cut) 0 else 0

def stitchData (a : BlocksData) : MatrixData :=
  (List.range (a.1*a.2.1.length+a.2.2.length)).map (fun i =>
    (List.range (a.1*a.2.1.length+a.2.2.length)).map (fun j => stitchEntry ((a,i),j)))

abbrev stitchCode := prodCode (prodCode blocksCode natCode) natCode
abbrev stFirst := first (prodCode blocksCode natCode) natCode
abbrev stBlocks := stFirst.then (first blocksCode natCode)
abbrev stI := stFirst.then (second blocksCode natCode)
abbrev stJ := second (prodCode blocksCode natCode) natCode
abbrev stN := stBlocks.then (first natCode (prodCode (listCode matrixCode) vectorCode))
abbrev stTail := stBlocks.then (second natCode (prodCode (listCode matrixCode) vectorCode))
abbrev stMatrices := stTail.then (first (listCode matrixCode) vectorCode)
abbrev stScalars := stTail.then (second (listCode matrixCode) vectorCode)
def stK := stMatrices.then (lengthList matrixCode)
instance poly_stK : PolyTime stK := by unfold stK;infer_instance
def stCut := stN.nmul stK
instance poly_stCut : PolyTime stCut := by unfold stCut;infer_instance

def stitchedMatrixEntry :=
  let block := ((stI.nmod stK).both stMatrices).then (getD matrixCode [])
  (block.both ((stI.ndiv stK).both (stJ.ndiv stK))).then matrixEntry
instance poly_stitchedMatrixEntry : PolyTime stitchedMatrixEntry := by
  have : PolyTime stI := by infer_instance
  have : PolyTime stJ := by infer_instance
  have : PolyTime stMatrices := by infer_instance
  unfold stitchedMatrixEntry;infer_instance

def stitchProgramEntry : Realizes stitchCode ratCode stitchEntry :=
  let zero := constant stitchCode ratCode 0
  let diag := ((stI.nsub stCut).both stScalars).then (getD ratCode 0)
  ((stI.nlt stCut).ite
    ((stJ.nlt stCut).ite (((stI.nmod stK).neq (stJ.nmod stK)).ite stitchedMatrixEntry zero) zero)
    ((stI.neq stJ).ite diag zero)).congr (by intro p;simp [stitchEntry])
instance poly_stitchProgramEntry : PolyTime stitchProgramEntry := by
  have : PolyTime stI := by infer_instance
  have : PolyTime stJ := by infer_instance
  have : PolyTime stScalars := by infer_instance
  unfold stitchProgramEntry;infer_instance

def stitchProgram : Realizes blocksCode matrixCode stitchData :=
  let tail := second natCode (prodCode (listCode matrixCode) vectorCode)
  let n := first natCode (prodCode (listCode matrixCode) vectorCode)
  let k := tail.then (first (listCode matrixCode) vectorCode) |>.then (lengthList matrixCode)
  let l := tail.then (second (listCode matrixCode) vectorCode) |>.then (lengthList ratCode)
  let dim := (n.nmul k).nadd l
  (((identity blocksCode).both dim).both dim).then stitchProgramEntry.matrixTabulate
instance poly_stitchProgram : PolyTime stitchProgram := by
  unfold stitchProgram
  apply poly_then

variable {n k l : ℕ}
lemma stitch_top (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (i j : Fin n) (b c : Fin k) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),b.val+k*i.val),c.val+k*j.val)=
      if b=c then B b i j else 0 := by
  have hi := (finProdFinEquiv (i,b)).isLt
  have hj := (finProdFinEquiv (j,c)).isLt
  change b.val+k*i.val<n*k at hi
  change c.val+k*j.val<n*k at hj
  have hk : 0 < k := by omega
  simp only [stitchEntry,List.length_ofFn,ite_eq_left hi,ite_eq_left hj]
  simp only [Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt b.isLt,
    Nat.mod_eq_of_lt c.isLt,Nat.add_mul_div_left _ _ hk,Nat.div_eq_of_lt b.isLt,
    Nat.div_eq_of_lt c.isLt,Nat.zero_add]
  rw [getD_ofFn,matrixData,getD_ofFn,getD_ofFn]
  simp [Fin.ext_iff]

lemma stitch_top_bottom (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (i : Fin n) (b : Fin k) (s : Fin l) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),b.val+k*i.val),n*k+s.val)=0 := by
  have hi := (finProdFinEquiv (i,b)).isLt
  change b.val+k*i.val<n*k at hi
  simp [stitchEntry,hi]

lemma stitch_bottom_top (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (s : Fin l) (j : Fin n) (c : Fin k) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),n*k+s.val),c.val+k*j.val)=0 := by
  have hj := (finProdFinEquiv (j,c)).isLt
  change c.val+k*j.val<n*k at hj
  have hne : n*k+s.val≠c.val+k*j.val := by omega
  simp [stitchEntry,hne]

lemma stitch_bottom (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (s t : Fin l) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),n*k+s.val),n*k+t.val)=
      if s=t then D s else 0 := by
  have hnot : ¬ n*k+s.val<n*k := by omega
  simp only [stitchEntry,List.length_ofFn,ite_eq_right hnot,
    Nat.add_left_cancel_iff,Nat.add_sub_cancel_left]
  rw [getD_ofFn]
  simp [Fin.ext_iff]

def blockRowEquiv {U S : Type*} (eb : U ≃ Fin k) (es : S ≃ Fin l) :
    ((Fin n × U) ⊕ S) ≃ Fin (n*k+l) :=
  ((((Equiv.refl (Fin n)).prodCongr eb).trans finProdFinEquiv).sumCongr es).trans finSumFinEquiv

@[simp] lemma blockRowEquiv_left {U S : Type*} (eb : U ≃ Fin k) (es : S ≃ Fin l)
    (i : Fin n) (b : U) : (blockRowEquiv eb es (.inl (i,b))).val=(eb b).val+k*i.val := rfl
@[simp] lemma blockRowEquiv_right {U S : Type*} (eb : U ≃ Fin k) (es : S ≃ Fin l)
    (s : S) : (blockRowEquiv (n:=n) eb es (.inr s)).val=n*k+(es s).val := rfl

lemma stitch_data {U S : Type*} [DecidableEq U] [DecidableEq S]
    (eb : U ≃ Fin k) (es : S ≃ Fin l)
    (B : U → Matrix (Fin n) (Fin n) ℚ) (D : S → ℚ) :
    stitchData (n,(List.ofFn (fun i => matrixData (B (eb.symm i))),List.ofFn (fun i => D (es.symm i))))=
      matrixData ((Matrix.fromBlocks (Matrix.blockDiagonal B) 0 0 (Matrix.diagonal D)).submatrix
        (blockRowEquiv eb es).symm (blockRowEquiv eb es).symm) := by
  simp only [stitchData,List.length_ofFn,range_map_fin]
  conv_rhs => unfold matrixData
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  obtain ⟨i,rfl⟩ := (blockRowEquiv eb es).surjective i
  obtain ⟨j,rfl⟩ := (blockRowEquiv eb es).surjective j
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rcases i with ⟨i,b⟩ | s <;> rcases j with ⟨j,c⟩ | t
  · simp only [blockRowEquiv_left]
    rw [stitch_top]
    simp [Matrix.blockDiagonal,eb.injective.eq_iff]
  · simp only [blockRowEquiv_left,blockRowEquiv_right]
    rw [stitch_top_bottom]
    rfl
  · simp only [blockRowEquiv_left,blockRowEquiv_right]
    rw [stitch_bottom_top]
    rfl
  · simp only [blockRowEquiv_right]
    rw [stitch_bottom]
    simp [Matrix.diagonal_apply,es.injective.eq_iff]
end CurrentKS.Realization
end

end OAI
