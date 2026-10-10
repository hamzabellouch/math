import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FacePoint
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack4
import OAI.Combinatorics.KMedianRecovery.Recovery.FaceSelection

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic Matrix
namespace Rectangular
open WordList RationalMatrix

def encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : List Bool :=
  WordList.encode (List.ofFn (fun i=>rowEncode (A i)))
lemma columnOp_encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (j : Fin n) :
    columnOp (pairBits (encode A,j.val.bits))=rowEncode (fun i=>A i j) := by
  simp only [columnOp,Function.comp_apply,swapWords,discardPrefix_pairBits,extractPrefix_pairBits,
    encode,mapWith_ofFn,rowEncode_eq,lookup_ofFn]
noncomputable def transpose (x : List Bool) : List Bool :=
  mapWith columnOp (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x)))
noncomputable def transpose_computes : PolyComputes transpose := by
  unfold transpose
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (discardPrefix input,BinaryEllipsoidInitial.indices (extractPrefix input)))
      (g:=mapWith columnOp)
      (discardPrefix_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes))
      transposeMap_computes)
lemma transpose_encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    transpose (pairBits (List.replicate n true,encode A))=encode A.transpose := by
  simp only [transpose,discardPrefix_pairBits,extractPrefix_pairBits,
    BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn,columnOp_encode]
  rfl
lemma rightRowOp_encode {m n : ℕ} (Bt : Matrix (Fin n) (Fin m) ℚ) (u : Fin m → ℚ) :
    rightRowOp (pairBits (encode Bt,rowEncode u))=rowEncode (fun j=>∑ i,u i*Bt j i) := by
  simp only [rightRowOp,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [encode,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun j=>RationalArray.dotListsWords (pairBits (rowEncode u,rowEncode (Bt j)))))=_
  simp only [dotListsWords_ofFn]
  exact (rowEncode_eq _).symm
lemma gram_encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    mapWith rightRowOp (pairBits (encode A.transpose,encode A.transpose))=RationalMatrix.encode (A.transpose*A) := by
  conv_lhs => rw [show encode A.transpose=WordList.encode (List.ofFn (fun i=>rowEncode (A.transpose i))) from rfl]
  rw [mapWith_ofFn]
  change WordList.encode (List.ofFn (fun i=>rightRowOp (pairBits (encode A.transpose,rowEncode (A.transpose i)))))=_
  simp only [rightRowOp_encode]
  rfl
lemma mulVec_encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) :
    RationalMatrix.mulVec (pairBits (encode A,rowEncode v))=rowEncode (A *ᵥ v) := by
  simp only [RationalMatrix.mulVec,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    encode,mapWith_ofFn,dotRow,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    dotListsWords_ofFn]
  simp only [rowEncode_eq]
  rfl
end Rectangular
end

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def coeffs (x : List Bool) : List Bool := mapWith BinaryRow.coeff (pairBits ([],x))
noncomputable def coeffs_computes : PolyComputes coeffs := by
  unfold coeffs
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith BinaryRow.coeff)
      ((const_computes []).pair id_computes) (mapWith_computes BinaryRow.coeff_computes))
lemma coeffs_encode {n : ℕ} (qs : List (Row n)) : coeffs (BinaryRow.rowsEncode qs)=Rectangular.encode (rowMatrix qs) := by
  simp only [coeffs,BinaryRow.rowsEncode,mapWith_encode,List.map_map,Function.comp_def,
    BinaryRow.coeff,discardPrefix_pairBits,BinaryRow.encode,extractPrefix_pairBits,
    Rectangular.encode]
  congr 1
  exact (List.ofFn_getElem_eq_map qs (fun q=>rowEncode q.coeff)).symm
noncomputable def bounds (x : List Bool) : List Bool := mapWith BinaryRow.bound (pairBits ([],x))
noncomputable def bounds_computes : PolyComputes bounds := by
  unfold bounds
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith BinaryRow.bound)
      ((const_computes []).pair id_computes) (mapWith_computes BinaryRow.bound_computes))
lemma bounds_encode {n : ℕ} (qs : List (Row n)) : bounds (BinaryRow.rowsEncode qs)=rowEncode (rowBounds qs) := by
  simp only [bounds,BinaryRow.rowsEncode,mapWith_encode,List.map_map,Function.comp_def,
    BinaryRow.bound,discardPrefix_pairBits,BinaryRow.encode,rowEncode_eq,rowBounds]
  congr 1
  exact (List.ofFn_getElem_eq_map qs (fun q=>BinaryRational.encode q.bound)).symm
noncomputable def transposed (x : List Bool) : List Bool :=
  Rectangular.transpose (pairBits (first x,coeffs (BinaryFinalFace.run x)))
noncomputable def transposed_computes : PolyComputes transposed := by
  unfold transposed
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (first input,(coeffs ∘ BinaryFinalFace.run) input))
      (g:=Rectangular.transpose)
      (first_computes.pair
        (PolyComputes.comp (f:=BinaryFinalFace.run) (g:=coeffs) BinaryFinalFace.run_computes coeffs_computes))
      Rectangular.transpose_computes)
lemma transposed_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    transposed (pack rs B)=Rectangular.encode (rowMatrix (finalFace rs B)).transpose := by
  rw [transposed,(projections_pack rs B).1,BinaryFinalFace.run_pack,coeffs_encode,Rectangular.transpose_encode]
noncomputable def gram (x : List Bool) : List Bool := mapWith rightRowOp (pairBits (transposed x,transposed x))
noncomputable def gram_computes : PolyComputes gram := by
  unfold gram
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (transposed input,transposed input)) (g:=mapWith rightRowOp)
      (transposed_computes.pair transposed_computes) mulMap_computes)
lemma gram_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    gram (pack rs B)=RationalMatrix.encode ((rowMatrix (finalFace rs B)).transpose*rowMatrix (finalFace rs B)) := by
  rw [gram,transposed_pack,Rectangular.gram_encode]
noncomputable def rhs (x : List Bool) : List Bool :=
  RationalMatrix.mulVec (pairBits (transposed x,bounds (BinaryFinalFace.run x)))
noncomputable def rhs_computes : PolyComputes rhs := by
  unfold rhs
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (transposed input,(bounds ∘ BinaryFinalFace.run) input))
      (g:=RationalMatrix.mulVec)
      (transposed_computes.pair
        (PolyComputes.comp (f:=BinaryFinalFace.run) (g:=bounds) BinaryFinalFace.run_computes bounds_computes))
      mulVec_computes)
lemma rhs_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    rhs (pack rs B)=rowEncode ((rowMatrix (finalFace rs B)).transpose *ᵥ rowBounds (finalFace rs B)) := by
  rw [rhs,transposed_pack,BinaryFinalFace.run_pack,bounds_encode,Rectangular.mulVec_encode]
noncomputable def point (x : List Bool) : List Bool := solveWords (pairBits (gram x,rhs x))
noncomputable def point_computes : PolyComputes point := by
  unfold point
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (gram input,rhs input)) (g:=solveWords)
      (gram_computes.pair rhs_computes) solveWords_computes)
lemma point_pack {n : ℕ} (rs : List (Row n)) (B : ℕ)
    (hf : ∃ x : Fin n → ℝ, (∀ q∈rs,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    point (pack rs B)=rowEncode (facePoint rs B) := by
  rw [point,gram_pack,rhs_pack,solveWords_bird]
  congr 1
  let C := rowMatrix (finalFace rs B)
  have hC := finalFace_rat_injective rs B hf
  have hG : (C.transpose*C).PosDef := by simpa using PosDef.conjTranspose_mul_self C hC
  have he : BirdRational.solve (C.transpose*C) (C.transpose *ᵥ rowBounds (finalFace rs B))=
      PositiveSolve.solve n (C.transpose*C) (C.transpose *ᵥ rowBounds (finalFace rs B)) := by
    apply mulVec_injective_of_isUnit hG.isUnit
    rw [BirdRational.solve_correct _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit).ne_zero,
      PositiveSolve.solve_correct n _ _ hG]
  simpa only [facePoint,PositiveSolve.freezeMat_eq,PositiveSolve.freezeVec_eq] using he
noncomputable def run (x : List Bool) : List Bool :=
  if (BinaryRationalDecision.run x).head?.getD false then true::point x else []
noncomputable def run_computes : PolyComputes run :=
  (BinaryRationalDecision.run_computes.comp MetricKMedianRecovery.BitMachine.head_computes).cond
    (point_computes.comp (prefix_computes true)) (const_computes [])
def resultBits {n : ℕ} : Option (Fin n → ℚ) → List Bool
  | none=>[]
  | some v=>true::rowEncode v
lemma run_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    run (pack rs B)=resultBits (exactSolve rs B) := by
  rw [run,BinaryRationalDecision.run_pack]
  simp only [List.head?_cons,Option.getD_some,exactSolve]
  split_ifs with h
  · rw [point_pack rs B ((boundedRationalDecide_correct rs B).mp h)]
    simp only [h,ite_true,resultBits]
  · simp [h,resultBits]

noncomputable def computation : Turing.TM2ComputableInPolyTime System.bits
    (fun p : (n : ℕ) × Option (Fin n → ℚ)=>resultBits p.2)
    (fun p : System=>⟨p.dimension,exactSolve p.constraints p.boxBound⟩) :=
  run_computes.reencode _ _ (fun p=>run_pack p.constraints p.boxBound)
lemma sound {n : ℕ} (rs : List (Row n)) (B : ℕ) (v : Fin n → ℚ)
    (hv : exactSolve rs B=some v) : (∀ q∈rs,q.Holds v) ∧ (∀ j,|v j|≤(B:ℚ)) :=
  exactSolve_some rs B v hv
lemma complete {n : ℕ} (rs : List (Row n)) (B : ℕ)
    (hf : ∃ x : Fin n → ℝ, (∀ q∈rs,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ v, exactSolve rs B=some v := exactSolve_complete rs B hf
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
