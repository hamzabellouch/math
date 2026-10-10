import OAI.Analysis.Laughlin.Spin.Torus
import OAI.Analysis.Laughlin.Tensor.PolynomialRealization

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def generalSpinMatrix (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ :=
  (symmetricTensorInclusion Q)ᴴ * tensorMatrix Q A * symmetricTensorInclusion Q

theorem general_tensor_spin_intertwining (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    symmetricTensorInclusion Q*generalSpinMatrix Q A = tensorMatrix Q A*symmetricTensorInclusion Q := by
  ext a p
  let v : (Fin Q → Fin 2) → ℂ := fun b => symmetricTensorInclusion Q b p
  have hv : ∀ b c, tensorWeight Q b=tensorWeight Q c → v b=v c := by
    intro b c h
    simp only [v,symmetricTensorInclusion,Matrix.map_apply,symmetricTensorInclusionReal,h]
  have hf := tensorMatrix_preserves_symmetric Q A v hv
  have he := congrFun (symmetricTensor_projector_fixed Q (tensorMatrix Q A *ᵥ v) hf) a
  change (symmetricTensorInclusion Q*((symmetricTensorInclusion Q)ᴴ*tensorMatrix Q A*symmetricTensorInclusion Q)) a p = _
  calc
    _ = ((symmetricTensorInclusion Q*(symmetricTensorInclusion Q)ᴴ)*
      (tensorMatrix Q A*symmetricTensorInclusion Q)) a p := by simp only [Matrix.mul_assoc]
    _ = _ := he

theorem generalSpinMatrix_mul (Q : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    generalSpinMatrix Q (A*B) = generalSpinMatrix Q A*generalSpinMatrix Q B := by
  unfold generalSpinMatrix
  rw [tensorMatrix_mul]
  have he := general_tensor_spin_intertwining Q B
  unfold generalSpinMatrix at he
  calc
    _ = (symmetricTensorInclusion Q)ᴴ*tensorMatrix Q A*
      (tensorMatrix Q B*symmetricTensorInclusion Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← he]; simp only [Matrix.mul_assoc]

theorem generalSpinMatrix_one (Q : ℕ) : generalSpinMatrix Q 1=1 := by
  simp [generalSpinMatrix,tensorMatrix_one,symmetricTensorInclusion_isometry]

theorem generalSpinMatrix_source (Q : ℕ) (g : SourceSU2) :
    generalSpinMatrix Q g.val=sourceSpinRepresentation Q g := rfl

theorem generalSpinMatrix_diagonal (Q : ℕ) (x y : ℂ) :
    generalSpinMatrix Q (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) =
      Matrix.diagonal (fun p : Fin (Q+1) => y^p.val*x^(Q-p.val)) := by
  unfold generalSpinMatrix
  rw [tensorMatrix_diagonal,Matrix.mul_assoc,
    symmetricTensor_diagonal_intertwining Q (fun k => y^k*x^(Q-k)),
    ← Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.one_mul]

theorem generalSpinMatrix_transpose (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    generalSpinMatrix Q Aᵀ=(generalSpinMatrix Q A)ᵀ := by
  have hI : (symmetricTensorInclusion Q)ᴴ=(symmetricTensorInclusion Q)ᵀ := by
    ext a b
    simp [symmetricTensorInclusion,Matrix.conjTranspose_apply,Matrix.transpose_apply]
  have hT : tensorMatrix Q Aᵀ=(tensorMatrix Q A)ᵀ := rfl
  simp only [generalSpinMatrix,hI,hT,Matrix.transpose_mul,Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

theorem generalSpinMatrix_polynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (u v : R) (p : Fin (Q+1)) :
    (∑ q : Fin (Q+1), f (generalSpinMatrix Q A q p) *
      (f (Real.sqrt (Q.choose q.val : ℝ) : ℂ) * v^q.val*u^(Q-q.val))) =
      f (Real.sqrt (Q.choose p.val : ℝ) : ℂ) *
        (f (A 0 1)*u+f (A 1 1)*v)^p.val *
        (f (A 0 0)*u+f (A 1 0)*v)^(Q-p.val) := by
  have h := general_tensor_spin_intertwining Q A
  have hm := congrArg (fun M : Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℂ =>
    ∑ a, f (M a p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) h
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul] at hm
  rw [Finset.sum_comm] at hm
  have hl (q : Fin (Q+1)) : (∑ a, f (symmetricTensorInclusion Q a q) *
      f (generalSpinMatrix Q A q p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      f (generalSpinMatrix Q A q p) *
        (f (Real.sqrt (Q.choose q.val : ℝ) : ℂ)*v^q.val*u^(Q-q.val)) := by
    simp_rw [mul_right_comm _ (f (generalSpinMatrix Q A q p)), ← Finset.sum_mul]
    rw [symmetricTensor_weighted_column f Q q (fun n => v^n*u^(Q-n))]
    ring
  simp_rw [hl] at hm
  rw [Finset.sum_comm] at hm
  have hr (b : Fin Q → Fin 2) : (∑ a, f (tensorMatrix Q A a b) *
      f (symmetricTensorInclusion Q b p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      f (symmetricTensorInclusion Q b p) *
        ((f (A 0 1)*u+f (A 1 1)*v)^(tensorWeight Q b) *
        (f (A 0 0)*u+f (A 1 0)*v)^(Q-tensorWeight Q b)) := by
    simp_rw [mul_right_comm _ (f (symmetricTensorInclusion Q b p)), ← Finset.sum_mul]
    rw [tensorMatrix_polynomial]
    ring
  simp_rw [hr] at hm
  rw [symmetricTensor_weighted_column f Q p (fun n =>
    (f (A 0 1)*u+f (A 1 1)*v)^n*(f (A 0 0)*u+f (A 1 0)*v)^(Q-n))] at hm
  simpa only [mul_assoc] using hm

end Laughlin.Rotation

end OAI
