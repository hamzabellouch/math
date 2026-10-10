import OAI.MeasureTheory.Falconer.Fourier.MatrixCofactorBound
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # Actual coordinate isomorphisms for a transverse tuple in arbitrary dimension -/

namespace Falconer
open scoped BigOperators Matrix
variable {d : ℕ}

noncomputable def euclideanColumnMatrix (v : Fin d → Space d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun i j => (v j) i)

noncomputable def euclideanColumnLinear (v : Fin d → Space d) : Space d →ₗ[ℝ] Space d where
  toFun x := ∑ i : Fin d, x i • v i
  map_add' x y := by simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

theorem euclideanColumnLinear_apply (v : Fin d → Space d) (x : Space d) (i : Fin d) :
    euclideanColumnLinear v x i = (euclideanColumnMatrix v *ᵥ WithLp.ofLp x) i := by
  simp only [euclideanColumnLinear,LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    smul_eq_mul,Matrix.mulVec,dotProduct,euclideanColumnMatrix,Matrix.of_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

noncomputable def euclideanDualCoordinates (v : Fin d → Space d) (x : Space d) : Space d :=
  WithLp.toLp 2 ((euclideanColumnMatrix v)⁻¹ *ᵥ WithLp.ofLp x)

theorem euclideanDualCoordinates_column (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (x : Space d) :
    euclideanDualCoordinates v (euclideanColumnLinear v x) = x := by
  have he : WithLp.ofLp (euclideanColumnLinear v x) = euclideanColumnMatrix v *ᵥ WithLp.ofLp x :=
    funext (euclideanColumnLinear_apply v x)
  apply PiLp.ext
  intro i
  change ((euclideanColumnMatrix v)⁻¹ *ᵥ WithLp.ofLp (euclideanColumnLinear v x)) i = x i
  rw [he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hv),Matrix.one_mulVec]

noncomputable def euclideanColumnEquiv (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) : Space d ≃L[ℝ] Space d :=
  (LinearEquiv.ofBijective (euclideanColumnLinear v)
    (let hinj := Function.LeftInverse.injective (euclideanDualCoordinates_column v hv)
     ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩)).toContinuousLinearEquiv

@[simp] theorem euclideanColumnEquiv_apply (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (x : Space d) :
    euclideanColumnEquiv v hv x = euclideanColumnLinear v x := rfl

theorem euclideanColumnEquiv_symm_apply (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (x : Space d) :
    (euclideanColumnEquiv v hv).symm x = euclideanDualCoordinates v x := by
  have hh := euclideanDualCoordinates_column v hv ((euclideanColumnEquiv v hv).symm x)
  rw [← euclideanColumnEquiv_apply v hv,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem euclideanColumnMatrix_gram (v : Fin d → Space d) :
    Matrix.gram ℝ v = (euclideanColumnMatrix v)ᵀ * euclideanColumnMatrix v := by
  ext i j
  simp only [Matrix.gram_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    Matrix.mul_apply,Matrix.transpose_apply,euclideanColumnMatrix,Matrix.of_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem euclideanColumnMatrix_gram_sqrt (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = |(euclideanColumnMatrix v).det| := by
  rw [euclideanColumnMatrix_gram,Matrix.det_mul,Matrix.det_transpose,← pow_two,Real.sqrt_sq_eq_abs]

end Falconer

end OAI
