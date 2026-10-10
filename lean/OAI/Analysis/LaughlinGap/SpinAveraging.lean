import Mathlib
import OAI.Analysis.LaughlinGap.Averaging
import OAI.Analysis.LaughlinGap.IntertwiningSpin

namespace OAI

/-! Spin Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

noncomputable def loweringMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) : Matrix ι ι ℝ := LinearMap.toMatrix' S.lower

lemma loweringMatrix_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) : (loweringMatrix S).transpose = LinearMap.toMatrix' S.raise := by
  ext i j
  have he := S.adjoint (Pi.single i 1) (Pi.single j 1)
  simpa [loweringMatrix, LinearMap.toMatrix'_apply, dotProduct_single, single_dotProduct] using he

noncomputable def commutantLadderMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) {A : Matrix ι ι ℝ}
    (hA : A ∈ rotationCommutant (loweringMatrix S)) : LadderMap S S where
  toLinearMap := Matrix.toLin' A
  lower x := by
    have he := (rotationCommutant_mem _ _).mp hA |>.1
    have hh : loweringMatrix S * A = A * loweringMatrix S := sub_eq_zero.mp he
    have hr := congrArg (fun M : Matrix ι ι ℝ => Matrix.toLin' M x) hh
    simpa [loweringMatrix, Matrix.toLin'_mul] using hr
  raise x := by
    have he := (rotationCommutant_mem _ _).mp hA |>.2
    have hh : (loweringMatrix S).transpose * A = A * (loweringMatrix S).transpose :=
      sub_eq_zero.mp he
    rw [loweringMatrix_transpose] at hh
    have hr := congrArg (fun M : Matrix ι ι ℝ => Matrix.toLin' M x) hh
    simpa [Matrix.toLin'_mul] using hr

lemma ladderMap_matrix_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) (A : LadderMap S S) :
    LinearMap.toMatrix' A.toLinearMap ∈ rotationCommutant (loweringMatrix S) := by
  rw [rotationCommutant_mem]
  constructor
  · apply sub_eq_zero.mpr
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, loweringMatrix, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    exact A.lower x
  · apply sub_eq_zero.mpr
    rw [loweringMatrix_transpose]
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    exact A.raise x

lemma toMatrix_transposeMap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    LinearMap.toMatrix' (transposeMap A) = (LinearMap.toMatrix' A).transpose := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, transposeMap, Matrix.transpose_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  change dotProduct (A _) (Pi.single j 1) = _
  rw [dotProduct_single_one]
  apply congrArg (fun x : ι → ℝ => A x j)
  funext k
  by_cases hk : i=k <;> simp [hk, eq_comm]

noncomputable def tensorProjection {n m z : ℕ} (hz : z ≤ min n m) :
    Matrix (Fin (n+1) × Fin (m+1)) (Fin (n+1) × Fin (m+1)) ℝ :=
  LinearMap.toMatrix' ((coupledEmbedding hz).comp (coupledEmbedding hz).transpose).toLinearMap

lemma tensorProjection_mem {n m z : ℕ} (hz : z ≤ min n m) :
    tensorProjection hz ∈ rotationCommutant (loweringMatrix (tensorSpin n m)) :=
  ladderMap_matrix_mem _ _

lemma coupledEmbedding_entry {n m z : ℕ} (hz : z ≤ min n m)
    (a : Fin (n+1) × Fin (m+1)) (l : Fin (n+m-2*z+1)) :
    LinearMap.toMatrix' (coupledEmbedding hz).toLinearMap a l = coupledTensor n m z l.val a := by
  rw [LinearMap.toMatrix'_apply, coupledEmbedding_apply]
  simp [Pi.single_apply, ite_apply]

lemma tensorProjection_eq {n m z : ℕ} (hz : z ≤ min n m) :
    tensorProjection hz = ∑ l : Fin (n+m-2*z+1),
      Matrix.vecMulVec (coupledTensor n m z l.val) (coupledTensor n m z l.val) := by
  simp only [tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coupledEmbedding_entry,
    Matrix.sum_apply, Matrix.vecMulVec_apply]

lemma coupledTensor_dot {n m : ℕ} (i j : CoupledIndex n m) :
    dotProduct (coupledTensor n m i.1.val i.2.val) (coupledTensor n m j.1.val j.2.val) =
      if i=j then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (coupledFamily_orthonormal n m)) j i
  simpa only [coupledFamily, EuclideanSpace.inner_toLp_toLp, star_trivial, eq_comm] using hh

lemma tensorProjection_mulVec {n m z : ℕ} (hz : z ≤ min n m)
    (i : CoupledIndex n m) :
    (tensorProjection hz).mulVec (coupledTensor n m i.1.val i.2.val) =
      if i.1.val=z then coupledTensor n m i.1.val i.2.val else 0 := by
  rw [tensorProjection_eq]
  simp only [Matrix.sum_mulVec, Matrix.vecMulVec_mulVec]
  let z' : Fin (min n m+1) := ⟨z, by omega⟩
  have he (l : Fin (n+m-2*z+1)) :
      dotProduct (coupledTensor n m z l.val) (coupledTensor n m i.1.val i.2.val) =
      if (⟨z',l⟩ : CoupledIndex n m)=i then 1 else 0 := coupledTensor_dot ⟨z',l⟩ i
  simp only [he]
  split_ifs with hi
  · obtain ⟨w,k⟩ := i
    have hw : w=z' := Fin.ext hi
    subst w
    simp
    rfl
  · have hne (l : Fin (n+m-2*z+1)) : (⟨z',l⟩ : CoupledIndex n m) ≠ i := by
      intro he
      apply hi
      exact (congrArg (fun j : CoupledIndex n m => j.1.val) he).symm
    simp only [hne, ite_false, MulOpposite.op_zero, zero_smul, Finset.sum_const_zero]

lemma trace_mul_rankOne {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    (A * Matrix.vecMulVec x y).trace = dotProduct y (A.mulVec x) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem tensorSpin_average {n m : ℕ}
    (A : Matrix (Fin (n+1) × Fin (m+1)) (Fin (n+1) × Fin (m+1)) ℝ) :
    average (rotationCommutant (loweringMatrix (tensorSpin n m))) A =
      ∑ z : Fin (min n m+1),
        ((A * tensorProjection (Nat.le_of_lt_succ z.isLt)).trace /
          (n+m-2*z.val+1 : ℕ)) • tensorProjection (Nat.le_of_lt_succ z.isLt) := by
  classical
  let S := rotationCommutant (loweringMatrix (tensorSpin n m))
  let Y := average S A
  have hm : Y ∈ S := average_mem S A
  let L := commutantLadderMap (tensorSpin n m) hm
  let c : ℕ → ℝ := fun z => dotProduct (highestTensor n m z) (Y.mulVec (highestTensor n m z))
  have he (i : CoupledIndex n m) : Y.mulVec (coupledTensor n m i.1.val i.2.val) =
      c i.1.val • coupledTensor n m i.1.val i.2.val :=
    tensorSpin_schur (Nat.le_of_lt_succ i.1.isLt) (Nat.le_of_lt_succ i.2.isLt) L
  have ht (z : Fin (min n m+1)) :
      (A * tensorProjection (Nat.le_of_lt_succ z.isLt)).trace =
        (n+m-2*z.val+1 : ℕ) * c z.val := by
    rw [trace_mul_average S A (tensorProjection_mem (Nat.le_of_lt_succ z.isLt)),
      tensorProjection_eq, Matrix.mul_sum, Matrix.trace_sum]
    have hrow (l : Fin (n+m-2*z.val+1)) :
        (Y * Matrix.vecMulVec (coupledTensor n m z.val l.val)
          (coupledTensor n m z.val l.val)).trace = c z.val := by
      rw [trace_mul_rankOne, he ⟨z,l⟩, dotProduct_smul]
      rw [coupledTensor_dot (⟨z,l⟩ : CoupledIndex n m) ⟨z,l⟩]
      simp
    change (∑ l : Fin (n+m-2*z.val+1),
      (Y * Matrix.vecMulVec (coupledTensor n m z.val l.val)
        (coupledTensor n m z.val l.val)).trace) = _
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcoef (z : Fin (min n m+1)) :
      (A * tensorProjection (Nat.le_of_lt_succ z.isLt)).trace /
        (n+m-2*z.val+1 : ℕ) = c z.val := by
    rw [ht]
    have hd : ((n+m-2*z.val+1 : ℕ) : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_left₀ _ hd
  simp only [hcoef]
  apply Matrix.mulVec_injective
  funext x
  change Y.mulVec x = _
  nth_rw 1 [← coupledTensor_expansion n m x]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, he, smul_smul]
  rw [Matrix.sum_mulVec]
  have hx (z : Fin (min n m+1)) :
      (tensorProjection (Nat.le_of_lt_succ z.isLt)).mulVec x =
        ∑ l : Fin (n+m-2*z.val+1),
          dotProduct (coupledTensor n m z.val l.val) x • coupledTensor n m z.val l.val := by
    rw [tensorProjection_eq]
    simp [Matrix.sum_mulVec, Matrix.vecMulVec_mulVec]
  simp only [Matrix.smul_mulVec, hx, Finset.smul_sum, smul_smul]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  exact mul_comm _ _

end LaughlinGap.Spin

end

end OAI
