import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOptimize
import OAI.Analysis.MatrixSigning.Complexity.PolynomialExplicit
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceBasics
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixSum
import OAI.Analysis.MatrixSigning.Realization.VarianceRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance poly_mgView : PolyTime mgView := by unfold mgView;apply poly_reindex
instance poly_mgN : PolyTime mgN := by unfold mgN;apply poly_then
instance poly_mgRest : PolyTime mgRest := by unfold mgRest;apply poly_then
instance poly_mgM : PolyTime mgM := by unfold mgM;apply poly_then
instance poly_mgDen : PolyTime mgDen := by unfold mgDen;apply poly_then
instance poly_mgShift : PolyTime mgShift := by unfold mgShift;apply poly_changeOutput
instance poly_mgTest : PolyTime mgTest := by unfold mgTest;apply poly_congr
instance poly_gridStep : PolyTime gridStep := by
  unfold gridStep
  apply PolyTime.both
  · infer_instance
  · apply PolyTime.both
    · infer_instance
    · apply PolyTime.ite <;> infer_instance
lemma gridStep_iterate_bounds (s : MatrixGrid×(ℕ×ℕ)) (L n : ℕ)
    (h1 : s.2.1≤L) (h2 : s.2.2≤L) :
    (gridStepData^[n] s).1=s.1 ∧ (gridStepData^[n] s).2.1≤L+n ∧
      (gridStepData^[n] s).2.2≤L+n := by
  induction n with
  | zero => simp only [Function.iterate_zero,id_eq,Nat.add_zero];exact ⟨trivial,h1,h2⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [gridStepData]
    refine ⟨ih.1,by omega,?_⟩
    split <;> omega
instance size_gridStep : IterateSize gridStep := by
  refine ⟨⟨10*X+10,?_⟩⟩
  intro s n
  let L := (gridStateCode s).length
  have hp : (matrixGridCode s.1).length≤L := le_prodCode_left s
  have h1 : s.2.1≤L := by
    have h := (le_prodCode_left (ea:=natCode) (eb:=natCode) s.2).trans (le_prodCode_right (ea:=matrixGridCode) s)
    simpa only [natCode,List.length_replicate] using h
  have h2 : s.2.2≤L := by
    have h := (le_prodCode_right (ea:=natCode) (eb:=natCode) s.2).trans (le_prodCode_right (ea:=matrixGridCode) s)
    simpa only [natCode,List.length_replicate] using h
  have h := gridStep_iterate_bounds s L n h1 h2
  change (gridStateCode (gridStepData^[n] s)).length≤10*(L+n)+10
  simp only [gridStateCode,prodCode_length,natCode,List.length_replicate,h.1]
  omega
instance poly_gridUpper : PolyTime gridUpper := by unfold gridUpper;apply poly_congr
instance poly_fVariance : PolyTime fVariance := by unfold fVariance;apply poly_congr

lemma isPoly_faceD : IsPoly (fun p : FaceParams => (faceCode p).length) FaceParams.d := by
  have h := (RunsPoly.of_poly fD id (isPoly_self _)).output
  simp only [natCode,List.length_replicate,id_eq] at h
  exact h
lemma isPoly_faceN : IsPoly (fun p : FaceParams => (faceCode p).length) FaceParams.N := by
  have h := (RunsPoly.of_poly (fBase.then (lengthList ratCode)) id (isPoly_self _)).output
  simpa only [natCode,List.length_replicate,List.length_ofFn,id_eq] using h
lemma varianceDen_ceil (p : FaceParams) :
    ⌈(p.N:ℚ)*1000*(p.d:ℚ)^2⌉₊=1000*p.N*p.d^2 := by
  have he : (p.N:ℚ)*1000*(p.d:ℚ)^2=((1000*p.N*p.d^2:ℕ):ℚ) := by push_cast;ring
  rw [he,Nat.ceil_natCast]
instance poly_varianceDen : PolyTime
    (((((fBase.then (lengthList ratCode)).then natToRat).mul (constant faceCode ratCode 1000)).mul
      ((fD.then natToRat).pow 2)).then ratCeil) := by
  have he : IsPoly (fun p : FaceParams => (faceCode p).length)
      (fun p => ⌈((List.ofFn p.base).length:ℚ)*1000*(p.d:ℚ)^2⌉₊) := by
    simp only [List.length_ofFn,varianceDen_ceil]
    exact ((isPoly_const _ 1000).mul isPoly_faceN).mul (isPoly_faceD.pow 2)
  have h := RunsPoly.then_with
    (RunsPoly.of_poly ((((fBase.then (lengthList ratCode)).then natToRat).mul (constant faceCode ratCode 1000)).mul
      ((fD.then natToRat).pow 2)) id (isPoly_self _))
    (fun hw => runsPoly_ratCeil _ hw he)
  exact ⟨h.cost⟩
instance poly_fVarianceGrid : PolyTime fVarianceGrid := by unfold fVarianceGrid;apply poly_changeOutput
instance poly_varianceQuery : PolyTime varianceQuery := by unfold varianceQuery;apply poly_then
instance poly_faceNormalized : PolyTime faceNormalized := by unfold faceNormalized;apply poly_changeOutput
end CurrentKS.Realization

end OAI
