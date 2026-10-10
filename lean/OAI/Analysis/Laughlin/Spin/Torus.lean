import OAI.Analysis.Laughlin.Spin.Representation
import OAI.Analysis.Laughlin.Tensor.WeightProducts

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def sourceTorus (z : ℂ) (hz : ‖z‖=1) : SourceSU2 := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i=0 then z else star z)
  have hzz : z*(starRingEnd ℂ) z=1 := by simpa [hz] using Complex.mul_conj' z
  have hzz' : (starRingEnd ℂ) z*z=1 := by rw [mul_comm]; exact hzz
  refine ⟨A,?_⟩
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A,Matrix.mul_apply,Matrix.star_eq_conjTranspose,hzz,hzz']
  · simp [A,Matrix.det_diagonal,Fin.prod_univ_two,hzz]

 theorem symmetricTensor_diagonal_intertwining (Q : ℕ) (f : ℕ → ℂ) :
    Matrix.diagonal (fun a => f (tensorWeight Q a))*symmetricTensorInclusion Q =
      symmetricTensorInclusion Q*Matrix.diagonal (fun p : Fin (Q+1) => f p.val) := by
  ext a p
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,symmetricTensorInclusion,Matrix.map_apply,
    symmetricTensorInclusionReal]
  by_cases h : tensorWeight Q a=p.val
  · simp [h,mul_comm]
  · simp [h]

theorem sourceSpinRepresentation_torus (Q : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    sourceSpinRepresentation Q (sourceTorus z hz) =
      Matrix.diagonal (fun p : Fin (Q+1) => (star z)^p.val*z^(Q-p.val)) := by
  change (symmetricTensorInclusion Q)ᴴ * tensorMatrix Q
    (Matrix.diagonal (fun i : Fin 2 => if i=0 then z else star z)) * symmetricTensorInclusion Q = _
  rw [tensorMatrix_diagonal,Matrix.mul_assoc,symmetricTensor_diagonal_intertwining Q (fun k => (star z)^k*z^(Q-k)),
    ← Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.one_mul]

end Laughlin.Rotation

end OAI
