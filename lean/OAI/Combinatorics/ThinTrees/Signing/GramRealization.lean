import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.ScalarRealization
import OAI.Combinatorics.ThinTrees.Pencil.PointPrograms
import OAI.Combinatorics.ThinTrees.RationalMatrix.InverseRealization
import OAI.Combinatorics.ThinTrees.Signing.GramWhitening

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

abbrev GramLift := MatrixData × MatrixObject
abbrev gramLiftCode := prodCode matrixCode matrixObjectCode
abbrev gramChild := first matrixCode matrixObjectCode
abbrev gramParent := second matrixCode matrixObjectCode

def firstColumn : Realizes matrixCode vectorCode
    (fun A : MatrixData => A.map (fun row => row.getD 0 0)) :=
  (((constant vectorCode natCode 0).both (identity vectorCode)).then (getD ratCode 0)).map
instance poly_firstColumn : PolyTime firstColumn := by unfold firstColumn;infer_instance

lemma firstColumn_data {n m : ℕ} (A : Matrix (Fin n) (Fin (m+1)) ℚ) :
    (matrixData A).map (fun row => row.getD 0 0)=List.ofFn (fun i => A i 0) := by
  simp only [matrixData,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  exact getD_ofFn (A i) 0 0

def gramLiftData (p : GramLift) : MatrixData :=
  (RationalGram.scalarFactors (((matrixData p.2.2).getD 0 []).getD 0 0)⁻¹).map
    (fun a => ((matrixData p.2.2).map (fun row => row.getD 0 0)).map (fun q => a*q)) ++
    p.1.map (fun row => 0::row)

def gramLift : Realizes gramLiftCode matrixCode gramLiftData :=
  let A := gramParent.then matrixEntries
  let z := constant gramLiftCode natCode 0
  let pivot := (A.both (z.both z)).then matrixEntry
  let factors := (((constant gramLiftCode ratCode 1).div pivot).then scalarFactorProgram)
  let scale := ((second vectorCode ratCode).both (first vectorCode ratCode)).then vectorScale
  let cap := ((A.then firstColumn).both factors).then scale.mapCtx
  let lift := ((constant vectorCode ratCode 0).both (identity vectorCode)).then (consList ratCode)
  ((cap.both (gramChild.then lift.map)).then (appendList vectorCode)).congr
    (fun _ => by simp only [gramLiftData,one_div,id_eq])
instance poly_gramLift : PolyTime gramLift := by
  unfold gramLift
  apply poly_congr

lemma gramLift_data {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (xs : List (Fin n → ℚ)) :
    gramLiftData (xs.map List.ofFn,⟨n+1,A⟩)=
      ((RationalGram.scalarFactors (A 0 0)⁻¹).map (fun a i => a*A i 0) ++
        xs.map (Fin.cons 0)).map List.ofFn := by
  unfold gramLiftData
  have hp : ((matrixData A).getD 0 []).getD 0 0=A 0 0 := matrix_entry_data A 0 0
  rw [hp,firstColumn_data]
  simp only [List.map_append,List.map_map,List.map_ofFn,Function.comp_def,List.ofFn_succ,
    Fin.cons_zero,Fin.cons_succ,List.map_cons, List.map_ofFn]

lemma gram_fold_correct (a : MatrixObject) :
    (schurHistoryData a).foldl (fun B A => gramLiftData (B,A)) []=
      (RationalGram.factorColumns a.1 a.2).map List.ofFn := by
  rcases a with ⟨n,A⟩
  induction n with
  | zero => simp [schurHistoryData,RationalGram.factorColumns]
  | succ n ih =>
    simp only [schurHistoryData,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih,gramLift_data]
    rfl

def gramColumnsProgram : Realizes matrixObjectCode matrixCode
    (fun a => (RationalGram.factorColumns a.1 a.2).map List.ofFn) :=
  (((constant matrixObjectCode matrixCode []).both schurHistory).then gramLift.fold).congr
    gram_fold_correct

lemma gram_take_history (a : MatrixObject) (k : ℕ) :
    (schurHistoryData a |>.take k).foldl (fun B A => gramLiftData (B,A)) []=[] ∨
    ∃b∈schurHistoryData a,
      (schurHistoryData a |>.take k).foldl (fun B A => gramLiftData (B,A)) []=
        (RationalGram.factorColumns b.1 b.2).map List.ofFn := by
  rcases a with ⟨n,A⟩
  induction n generalizing k with
  | zero => simp [schurHistoryData]
  | succ n ih =>
    by_cases hk : k ≤ n
    · have he : (schurHistoryData ⟨n+1,A⟩).take k=
          (schurHistoryData ⟨n,KS.W17.schurTail A⟩).take k := by
        rw [schurHistoryData,List.take_append_of_le_length]
        simpa only [schurHistory_length] using hk
      rw [he]
      rcases ih k (KS.W17.schurTail A) with h|⟨b,hb,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,by simp only [schurHistoryData,List.mem_append,List.mem_singleton]; exact Or.inl hb,he⟩
    · rw [List.take_of_length_le (by rw [schurHistory_length]; change n+1 ≤ k; omega),gram_fold_correct]
      exact Or.inr ⟨⟨n+1,A⟩,by simp [schurHistoryData],rfl⟩

lemma SchurDesc.gram_wire {a b : MatrixObject} (h : SchurDesc a b)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    (matrixCode ((RationalGram.factorColumns b.1 b.2).map List.ofFn)).length ≤
      (3*a.1*(2*KS.W30.inverseBitBound a.1 (matrixObjectCode a).length+1))*
        (2*(a.1*(2*(4*(4*KS.W30.inverseBitBound a.1 (matrixObjectCode a).length+1)+7)+1))+1) := by
  have hn := h.dim
  obtain ⟨k,p,r,h⟩ := h
  obtain ⟨hl,hv⟩ := RationalGram.trace_factor_bounds a.2 hA (matrixObject_parts a) h
  let B := KS.W30.inverseBitBound a.1 (matrixObjectCode a).length
  have hw : ∀v∈RationalGram.factorColumns b.1 b.2,
      (vectorCode (List.ofFn v)).length≤a.1*(2*(4*(4*B+1)+7)+1) := by
    intro v h
    apply (listCode_length_bound (List.ofFn v) (4*(4*B+1)+7) ?_).trans
      (by rw [List.length_ofFn]; exact Nat.mul_le_mul_right _ hn)
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact (show QParts (4*B+1) (v i) from hv v h i).length
  apply (listCode_length_bound _ (a.1*(2*(4*(4*B+1)+7)+1)) ?_).trans ?_
  · intro row hr
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
    exact hw v hv
  · rw [List.length_map]
    apply Nat.mul_le_mul_right _
    exact hl.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn))

lemma runsPoly_gramColumns {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    RunsPoly L gramColumnsProgram a := by
  have hh := runsPoly_schurHistory a ha hA
  have hh' := (RunsPoly.of_poly (constant matrixObjectCode matrixCode []) a ha).both hh
  have hd : IsPoly L (fun i => (a i).1) := ha.mono (fun i => matrixObject_dim_le (a i))
  have hi : IsPoly L (fun i => KS.W30.inverseBitBound (a i).1 (matrixObjectCode (a i)).length) :=
    ((((isPoly_const L 6).mul (ha.add (isPoly_const L 1))).mul
      ((hd.add (isPoly_const L 1)).pow 3))).mono
        (fun i => KS.W30.inverseBitBound_le_polynomial _ _)
  have hb := (((isPoly_const L 3).mul hd).mul (((isPoly_const L 2).mul hi).add (isPoly_const L 1))).mul
    (((isPoly_const L 2).mul (hd.mul (((isPoly_const L 2).mul
      (((isPoly_const L 4).mul (((isPoly_const L 4).mul hi).add (isPoly_const L 1))).add
        (isPoly_const L 7))).add (isPoly_const L 1)))).add (isPoly_const L 1))
  obtain ⟨p,hp⟩ := hb
  have hfold := runsPoly_fold_of_poly gramLift (fun i => ([],schurHistoryData (a i)))
    hh'.output (show ∃p : NaturalPolynomial, _ from ⟨p,by
      intro i ys zs he
      have hy : ys=(schurHistoryData (a i)).take ys.length := by
        dsimp only at he
        rw [he,List.take_left]
      rw [hy]
      rcases gram_take_history (a i) ys.length with hz|⟨b,hb,he⟩
      · rw [hz]; exact Nat.zero_le _
      · rw [he]
        exact ((schurHistory_mem (a i) (hA i) b hb).gram_wire (hA i)).trans (hp i)⟩)
  unfold gramColumnsProgram
  exact (hh'.then hfold).congr _

def transposeRectData (p : ℕ×MatrixData) : MatrixData :=
  (List.range p.1).map (fun i => p.2.map (fun row => row.getD i 0))

def transposeRect : Realizes (prodCode natCode matrixCode) matrixCode transposeRectData :=
  let ec := prodCode natCode matrixCode
  let base := first ec natCode
  let rows := base.then (second natCode matrixCode)
  let i := second ec natCode
  let entry := (first natCode vectorCode).both (second natCode vectorCode)
  let row := ((i.both rows).then (entry.then (getD ratCode 0)).mapCtx)
  ((identity ec).both (first natCode matrixCode)).then row.tabulate
instance poly_transposeRect : PolyTime transposeRect := by
  unfold transposeRect
  apply poly_then

lemma transposeRect_data {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) :
    transposeRectData (m,matrixData A)=matrixData Aᵀ := by
  simp only [transposeRectData,range_map_fin,matrixData,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact getD_ofFn (A j) i 0

lemma gramColumns_transpose (a : MatrixObject) :
    transposeRectData (a.1,(RationalGram.factorColumns a.1 a.2).map List.ofFn)=
      matrixData (RationalGram.factorMatrix a.2) := by
  have hs : (RationalGram.factorColumns a.1 a.2).map List.ofFn=
      matrixData (RationalGram.factorMatrix a.2)ᵀ := by
    change (RationalGram.factorColumns a.1 a.2).map List.ofFn=
      List.ofFn (fun j => List.ofFn ((RationalGram.factorColumns a.1 a.2).get j))
    have he : List.map List.ofFn (List.ofFn (RationalGram.factorColumns a.1 a.2).get)=
        List.ofFn (List.ofFn ∘ (RationalGram.factorColumns a.1 a.2).get) := List.map_ofFn
    simpa only [List.ofFn_get,Function.comp_def] using he
  rw [hs,transposeRect_data,transpose_transpose]

def gramMatrixProgram : Realizes matrixObjectCode matrixCode
    (fun a => matrixData (RationalGram.factorMatrix a.2)) :=
  ((matrixDim.both gramColumnsProgram).then transposeRect).congr gramColumns_transpose

lemma runsPoly_gramMatrix {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    RunsPoly L gramMatrixProgram a := by
  unfold gramMatrixProgram
  apply RunsPoly.congr
  exact ((RunsPoly.of_poly matrixDim a ha).both (runsPoly_gramColumns a ha hA)).then_poly transposeRect

def whiteningProgram : Realizes matrixObjectCode matrixCode
    (fun a => matrixData (GramWhitening.rationalFactor a.2)) :=
  rationalInverseProgram.then gramMatrixProgram

lemma runsPoly_whitening {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L whiteningProgram a := by
  have hi := runsPoly_rationalInverse a ha hA
  unfold whiteningProgram
  apply hi.then
  apply runsPoly_gramMatrix _ hi.output
  intro i
  rw [RationalInverse.inverse_eq_of_cast _ (hA i),GramWhitening.cast_inverse]
  exact (hA i).inv.posSemidef

end CurrentKS.Realization
end

end OAI
