import Mathlib
import OAI.Combinatorics.ThinTrees.RationalMatrix.Inverse
import OAI.Combinatorics.ThinTrees.RationalMatrix.SchurHistory

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

abbrev BackSolve := MatrixData×MatrixObject
abbrev backSolveCode := prodCode matrixCode matrixObjectCode
abbrev solveChild := first matrixCode matrixObjectCode
abbrev solveParent := second matrixCode matrixObjectCode
abbrev solveColumnCode := prodCode backSolveCode natCode
abbrev solveColumnBase := first backSolveCode natCode
abbrev solveColumnIndex := second backSolveCode natCode
abbrev solveColumnA := solveColumnBase.then solveParent
abbrev solveColumnB := solveColumnBase.then solveChild
abbrev solveColumnDim := solveColumnA.then matrixDim
abbrev solveColumnEntries := solveColumnA.then matrixEntries

abbrev rhsCode := prodCode solveColumnCode natCode
abbrev rhsBase := first solveColumnCode natCode
abbrev rhsIndex := second solveColumnCode natCode

def solveRhs : Realizes rhsCode ratCode
    (fun p =>
      (if p.2+1=p.1.2 then 1 else 0)-
        ((matrixData p.1.1.2.2).getD (p.2+1) []).getD 0 0 *
          ((if 0=p.1.2 then 1 else 0)/((matrixData p.1.1.2.2).getD 0 []).getD 0 0)) :=
  let A := rhsBase.then solveColumnEntries
  let i := rhsIndex.then natSucc
  let j := rhsBase.then solveColumnIndex
  let zero := constant rhsCode natCode 0
  let ij := (i.both j).then identityEntry
  let zj := (zero.both j).then identityEntry
  let iz := (A.both (i.both zero)).then matrixEntry
  let zz := (A.both (zero.both zero)).then matrixEntry
  ij.sub (iz.mul (zj.div zz))
instance poly_solveRhs : PolyTime solveRhs := by unfold solveRhs;infer_instance

def solveTopRow : Realizes rhsCode ratCode
    (fun p => ((matrixData p.1.1.2.2).getD 0 []).getD (p.2+1) 0) :=
  let A := rhsBase.then solveColumnEntries
  let i := rhsIndex.then natSucc
  (A.both ((constant rhsCode natCode 0).both i)).then matrixEntry
instance poly_solveTopRow : PolyTime solveTopRow := by unfold solveTopRow;infer_instance

def liftColumnData (p : BackSolve×ℕ) : List ℚ :=
  let A := matrixData p.1.2.2
  let r := (List.range p.1.2.1.pred).map (fun i =>
    (if i+1=p.2 then 1 else 0)-(A.getD (i+1) []).getD 0 0*
      ((if 0=p.2 then 1 else 0)/(A.getD 0 []).getD 0 0))
  let y := matVecValue (p.1.1,r)
  let row := (List.range p.1.2.1.pred).map (fun i => (A.getD 0 []).getD (i+1) 0)
  ((if 0=p.2 then 1 else 0)-dotValue (row,y))/(A.getD 0 []).getD 0 0::y

def liftColumn : Realizes solveColumnCode vectorCode liftColumnData :=
  let n := solveColumnDim.then natPred
  let args := (identity solveColumnCode).both n
  let y := (solveColumnB.both (args.then solveRhs.tabulate)).then matVec
  let row := args.then solveTopRow.tabulate
  let zero := constant solveColumnCode natCode 0
  let b := (zero.both solveColumnIndex).then identityEntry
  let pivot := (solveColumnEntries.both (zero.both zero)).then matrixEntry
  (((b.sub ((row.both y).then dot)).div pivot).both y).then (consList ratCode)
instance poly_liftColumn : PolyTime liftColumn := by
  unfold liftColumn
  apply poly_then

lemma liftColumn_data {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (j : Fin (n+1)) :
    liftColumnData ((matrixData B,⟨n+1,A⟩),j.val)=
      List.ofFn (RationalInverse.liftSolve A B (Pi.single j (1 : ℚ))) := by
  have rhs : ((List.range n).map (fun i =>
      (if i+1=j.val then 1 else 0)-((matrixData A).getD (i+1) []).getD 0 0*
      ((if 0=j.val then 1 else 0)/((matrixData A).getD 0 []).getD 0 0)))=
      List.ofFn (fun i : Fin n => (Pi.single j (1 : ℚ) : Fin (n+1) → ℚ) i.succ-A i.succ 0*((Pi.single j (1 : ℚ) : Fin (n+1) → ℚ) 0/A 0 0)) := by
    rw [range_map_fin]
    apply congrArg List.ofFn
    funext i
    change (if i.succ.val=j.val then 1 else 0)-
      ((matrixData A).getD i.succ.val []).getD (0 : Fin (n+1)).val 0*
      ((if (0 : Fin (n+1)).val=j.val then 1 else 0)/
      ((matrixData A).getD (0 : Fin (n+1)).val []).getD (0 : Fin (n+1)).val 0)=_
    rw [matrix_entry_data,matrix_entry_data]
    simp only [Pi.single_apply,Fin.val_inj,eq_comm]
  have row : ((List.range n).map (fun i => ((matrixData A).getD 0 []).getD (i+1) 0))=
      List.ofFn (fun i : Fin n => A 0 i.succ) := by
    rw [range_map_fin]
    apply congrArg List.ofFn
    funext i
    exact matrix_entry_data A 0 i.succ
  change ((if 0=j.val then 1 else 0)-dotValue (_,matVecValue (matrixData B,_)))/
    ((matrixData A).getD 0 []).getD 0 0::matVecValue (matrixData B,_)=_
  dsimp only
  simp only [Nat.pred_succ]
  have pivot : ((matrixData A).getD 0 []).getD 0 0=A 0 0 := by
    simpa only [Fin.val_zero] using matrix_entry_data A 0 0
  rw [rhs,row,matVec_data,dot_ofFn,pivot]
  simp only [RationalInverse.liftSolve,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]
  congr 2
  simp only [Pi.single_apply,←Fin.val_inj,Fin.val_zero,eq_comm]

def inverseLiftData (p : BackSolve) : MatrixData :=
  transposeData ((List.range p.2.1).map (fun j => liftColumnData (p,j)))

def inverseLift : Realizes backSolveCode matrixCode inverseLiftData :=
  (((identity backSolveCode).both (solveParent.then matrixDim)).then liftColumn.tabulate).then transposeMatrix
instance poly_inverseLift : PolyTime inverseLift := by
  unfold inverseLift
  apply poly_then

lemma inverseLift_data {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) :
    inverseLiftData (matrixData B,⟨n+1,A⟩)=
      matrixData (fun i j => RationalInverse.liftSolve A B (Pi.single j (1 : ℚ)) i) := by
  unfold inverseLiftData
  rw [range_map_fin]
  simp only [liftColumn_data]
  change transposeData (matrixData (fun j i => RationalInverse.liftSolve A B (Pi.single j (1 : ℚ)) i))=_
  exact transpose_data _

lemma inverse_fold_correct (a : MatrixObject) :
    (schurHistoryData a).foldl (fun B A => inverseLiftData (B,A)) []=
      matrixData (RationalInverse.inverse a.1 a.2) := by
  rcases a with ⟨n,A⟩
  induction n with
  | zero => simp [schurHistoryData,RationalInverse.inverse,matrixData]
  | succ n ih =>
    simp only [schurHistoryData,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih,inverseLift_data]
    rfl

def rationalInverseProgram : Realizes matrixObjectCode matrixObjectCode
    (fun a => ⟨a.1,RationalInverse.inverse a.1 a.2⟩) :=
  (matrixDim.both (((constant matrixObjectCode matrixCode []).both schurHistory).then inverseLift.fold)).changeOutput
    matrixObjectCode (fun a => ⟨a.1,RationalInverse.inverse a.1 a.2⟩)
    (fun a => by rw [inverse_fold_correct];rfl)

lemma inverse_take_history (a : MatrixObject) (k : ℕ) :
    (schurHistoryData a |>.take k).foldl (fun B A => inverseLiftData (B,A)) []=[] ∨
    ∃b∈schurHistoryData a,
      (schurHistoryData a |>.take k).foldl (fun B A => inverseLiftData (B,A)) []=
        matrixData (RationalInverse.inverse b.1 b.2) := by
  rcases a with ⟨n,A⟩
  induction n generalizing k with
  | zero => simp [schurHistoryData]
  | succ n ih =>
    by_cases hk : k ≤ n
    · have he : (schurHistoryData ⟨n+1,A⟩).take k=
          (schurHistoryData ⟨n,KS.W17.schurTail A⟩).take k := by
        rw [schurHistoryData, List.take_append_of_le_length]
        simpa only [schurHistory_length] using hk
      rw [he]
      rcases ih k (KS.W17.schurTail A) with h|⟨b,hb,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,by simp only [schurHistoryData,List.mem_append,List.mem_singleton]; exact Or.inl hb,he⟩
    · rw [List.take_of_length_le (by rw [schurHistory_length]; change n+1 ≤ k; omega),inverse_fold_correct]
      exact Or.inr ⟨⟨n+1,A⟩,by simp [schurHistoryData],rfl⟩

lemma pivotTrace_posDef {N k t : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    {p : Fin k → Fin N} {r : Fin t → Fin N} {B : Matrix (Fin t) (Fin t) ℚ}
    (h : KS.W07.PivotTrace A p r B) (hA : A.PosDef) : B.PosDef := by
  induction h with
  | initial => exact hA
  | zero _ _ ih => exact RationalInverse.schur_posDef _ ih
  | positive _ _ ih => exact RationalInverse.schur_posDef _ ih

lemma SchurDesc.posDef {a b : MatrixObject} (h : SchurDesc a b) (hA : a.2.PosDef) : b.2.PosDef := by
  obtain ⟨k,p,r,h⟩ := h
  exact pivotTrace_posDef h hA

lemma matrixInverse_parts {n b : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀i j,QParts b (A i j)) (hp : A.PosDef) :
    ∀i j,QParts (KS.W30.inverseBitBound n b) (RationalInverse.inverse n A i j) := by
  intro i j
  rw [RationalInverse.inverse_eq A hp]
  have hh := KS.W30.rational_inverse_parts_size_le A b (fun i j => (h i j).1)
    (fun i j => (h i j).2) (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hp.isUnit)) i j
  exact ⟨(Nat.size_le.mp hh.1).le,(Nat.size_le.mp hh.2).le⟩

lemma SchurDesc.inverse_wire {a b : MatrixObject} (h : SchurDesc a b)
    (hA : a.2.PosDef) :
    (matrixCode (matrixData (RationalInverse.inverse b.1 b.2))).length ≤
      a.1*(2*(a.1*(2*(4*(32*((matrixObjectCode a).length+1)^7)+7)+1))+1) := by
  have hn := h.dim
  have hp := h.posDef hA
  obtain ⟨k,p,r,h⟩ := h
  have he := matrixInverse_parts b.2 (RationalGram.trace_parts h (matrixObject_parts a)) hp
  have hm := KS.W30.inverseBitBound_mono_dim (KS.W30.inverseBitBound a.1 (matrixObjectCode a).length) hn
  have hm' := hm.trans (KS.W30.inverseBitBound_twice_le_input_polynomial (matrixObject_dim_le a) le_rfl)
  have hb := matrixCode_parts_bound (RationalInverse.inverse b.1 b.2) (fun i j => (he i j).mono hm')
  exact hb.trans (Nat.mul_le_mul hn (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hn)) 1))

lemma runsPoly_rationalInverse {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L rationalInverseProgram a := by
  have hh := runsPoly_schurHistory a ha (fun i => (hA i).posSemidef)
  have hh' := (RunsPoly.of_poly (constant matrixObjectCode matrixCode []) a ha).both hh
  have hd : IsPoly L (fun i => (a i).1) := ha.mono (fun i => matrixObject_dim_le (a i))
  have hb := hd.mul (((isPoly_const L 2).mul (hd.mul (((isPoly_const L 2).mul
    (((isPoly_const L 4).mul ((isPoly_const L 32).mul ((ha.add (isPoly_const L 1)).pow 7))).add
      (isPoly_const L 7))).add (isPoly_const L 1)))).add (isPoly_const L 1))
  obtain ⟨p,hp⟩ := hb
  have hfold := runsPoly_fold_of_poly inverseLift (fun i => ([],schurHistoryData (a i)))
    hh'.output (show ∃p : NaturalPolynomial, _ from ⟨p,by
      intro i ys zs he
      have hy : ys=(schurHistoryData (a i)).take ys.length := by
        dsimp only at he
        rw [he,List.take_left]
      rw [hy]
      rcases inverse_take_history (a i) ys.length with hz|⟨b,hb,he⟩
      · rw [hz]; exact Nat.zero_le _
      · rw [he]
        exact ((schurHistory_mem (a i) (hA i).posSemidef b hb).inverse_wire
          (RationalInverse.posDef_of_cast _ (hA i))).trans (hp i)⟩)
  unfold rationalInverseProgram
  apply RunsPoly.changeOutput
  exact (RunsPoly.of_poly matrixDim a ha).both (hh'.then hfold)

end CurrentKS.Realization
end

end OAI
