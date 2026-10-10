import OAI.Probability.InvariantIsing.Haar.MatrixRotation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace OAI

/-! Matrix coordinates for Euclidean isometries and hyperplane reflections. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def rotationMatrix {N : ℕ} (R : Rotation N) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis R.toLinearMap

lemma rotationMatrix_apply {N : ℕ} (R : Rotation N) (i j : Fin N) :
    rotationMatrix R i j = R (EuclideanSpace.single j 1) i := by
  rw [rotationMatrix,LinearMap.toMatrix_apply]
  change (R (EuclideanSpace.basisFun (Fin N) ℝ j)) i = _
  rw [EuclideanSpace.basisFun_apply]

lemma rotationMatrix_mem {N : ℕ} (R : Rotation N) :
    rotationMatrix R ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  R.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin N) ℝ)
    (EuclideanSpace.basisFun (Fin N) ℝ)

lemma rotationMatrix_mul {N : ℕ} (R S : Rotation N) :
    rotationMatrix (R*S) = rotationMatrix R*rotationMatrix S := by
  exact LinearMap.toMatrix_mul _ _ _

@[simp] lemma rotationMatrix_one {N : ℕ} : rotationMatrix (1 : Rotation N) = 1 :=
  LinearMap.toMatrix_one _

@[simp] lemma rotationMatrix_specialRotation {N : ℕ} (U : SpecialOrthogonal N) :
    rotationMatrix (specialRotation U) = (U : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  rw [rotationMatrix_apply,specialRotation_apply]
  simp only [PiLp.single_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

def hyperplaneReflection {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) : Rotation N :=
  (ℝ ∙ v)ᗮ.reflection

@[simp] lemma hyperplaneReflection_zero {N : ℕ} :
    hyperplaneReflection (0 : EuclideanSpace ℝ (Fin N)) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  apply Submodule.reflection_mem_subspace_eq_self
  simp

lemma hyperplaneReflection_apply {N : ℕ} (v x : EuclideanSpace ℝ (Fin N)) :
    hyperplaneReflection v x = x-(2*(inner ℝ v x/‖v‖^2)) • v := by
  rw [hyperplaneReflection,Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  module

lemma rotationMatrix_reflection_apply {N : ℕ} (v : EuclideanSpace ℝ (Fin N))
    (i j : Fin N) :
    rotationMatrix (hyperplaneReflection v) i j =
      (1 : Matrix (Fin N) (Fin N) ℝ) i j-2*v i*v j/‖v‖^2 := by
  rw [rotationMatrix_apply,hyperplaneReflection_apply]
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.inner_single_right,PiLp.single_apply,starRingEnd_apply,
    star_trivial,one_mul]
  rw [Matrix.one_apply]
  split_ifs <;> ring

lemma rotationMatrix_reflection_det {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) (hv : v ≠ 0) :
    Matrix.det (rotationMatrix (hyperplaneReflection v)) = -1 := by
  rw [rotationMatrix,LinearMap.det_toMatrix,hyperplaneReflection,Submodule.det_reflection,
    Submodule.orthogonal_orthogonal,finrank_span_singleton hv,pow_one]

end InvariantIsing

end

end OAI
