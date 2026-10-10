import OAI.Analysis.CoulombTransport.CoulombCalculus
import OAI.Analysis.CoulombTransport.HessianCLM
import OAI.Analysis.CoulombTransport.StationaryEquation

namespace OAI

noncomputable section
open scoped RealInnerProductSpace
open Matrix

namespace Problem356.CoulombCalculus

/-- Unit coordinate vector for either local Coulomb branch. -/
def axisVector (k : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single k 1

@[simp] theorem norm_axisVector (k : Fin 3) : ‖axisVector k‖ = 1 := by
  simp [axisVector]

@[simp] theorem inner_axisVector (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    ⟪axisVector k, v⟫ = v k := by
  simp [axisVector, EuclideanSpace.inner_single_left]

/-- The analytic Coulomb Hessian at a coordinate axis is precisely the diagonal
matrix used in the finite-dimensional local nondegeneracy calculation. -/
theorem pairHessian_axisVector (k : Fin 3) :
    pairHessian (axisVector k) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  ext v i
  rw [pairHessian_apply_of_norm_eq_one (norm_axisVector k), inner_axisVector]
  change (-v + (3 * v k) • axisVector k) i =
    (LocalHessian.pairHessian k *ᵥ WithLp.ofLp v) i
  simp only [LocalHessian.pairHessian, Matrix.mulVec_diagonal]
  by_cases hi : i = k
  · subst i
    simp [LocalHessian.eigenvalue, axisVector]
    ring
  · simp [LocalHessian.eigenvalue, axisVector, hi]

@[simp] theorem axisVector_ne_zero (k : Fin 3) : axisVector k ≠ 0 := by
  intro h
  have hn := norm_axisVector k
  rw [h, norm_zero] at hn
  norm_num at hn

theorem pairHessian_axisVector_apply (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) :
    pairHessian (axisVector k) v i = LocalHessian.eigenvalue k i * v i := by
  rw [pairHessian_axisVector]
  change (LocalHessian.pairHessian k *ᵥ WithLp.ofLp v) i = _
  simp [LocalHessian.pairHessian, Matrix.mulVec_diagonal]

theorem pairHessian_neg_axisVector (k : Fin 3) :
    pairHessian (-axisVector k) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  rw [pairHessian_neg, pairHessian_axisVector]

theorem pairHessian_two_axisVector (k : Fin 3) :
    pairHessian ((2 : ℝ) • axisVector k) =
      (1 / 8 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  rw [pairHessian_smul_pos _ (by norm_num), pairHessian_axisVector]
  norm_num

theorem pairHessian_neg_two_axisVector (k : Fin 3) :
    pairHessian (-((2 : ℝ) • axisVector k)) =
      (1 / 8 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (LocalHessian.pairHessian k) := by
  rw [pairHessian_neg, pairHessian_two_axisVector]

end Problem356.CoulombCalculus

namespace Problem356.GeometryJets

open CoulombCalculus

/-- Identification of the center state derivative with the positive definite
operator verified by the explicit finite matrix calculation. -/
theorem centerStateHessian_axisVector (k : Fin 3) :
    centerStateHessian 20 (pairHessian (axisVector k)) = LocalHessian.stateOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    change ((2 : ℝ) • pairHessian (axisVector k) v.1 + (20 : ℝ) • v.1 -
      pairHessian (axisVector k) v.2) i = (LocalHessian.stateOperator k v).1 i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      pairHessian_axisVector_apply, LocalHessian.stateOperator_fst_apply]
    ring
  · ext i
    change (-pairHessian (axisVector k) v.1 +
      ((9 / 8 : ℝ) • pairHessian (axisVector k) v.2 + (20 : ℝ) • v.2)) i =
      (LocalHessian.stateOperator k v).2 i
    simp only [PiLp.neg_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      pairHessian_axisVector_apply, LocalHessian.stateOperator_snd_apply]
    ring

theorem centerParameterDerivative_axisVector (k : Fin 3) :
    centerParameterDerivative (pairHessian (axisVector k)) =
      LocalHessian.parameterOperator k := by
  rw [pairHessian_axisVector]
  unfold centerParameterDerivative LocalHessian.parameterOperator
  congr 2
  norm_num

/-- State partial derivative of the actual stationary field at an axis center. -/
theorem fderiv_stationary_axis_state (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
      (axisVector k, (0, -axisVector k)) ∘L
        ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =
      LocalHessian.stateOperator k := by
  rw [(hasFDerivAt_stationary_center 20 _ (norm_axisVector k)).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change centerParameterDerivative (pairHessian (axisVector k)) 0 +
    centerStateHessian 20 (pairHessian (axisVector k)) v = _
  simp [centerStateHessian_axisVector]

/-- Parameter partial derivative of the actual stationary field at an axis center. -/
theorem fderiv_stationary_axis_parameter (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
      (axisVector k, (0, -axisVector k)) ∘L
        ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =
      LocalHessian.parameterOperator k := by
  rw [(hasFDerivAt_stationary_center 20 _ (norm_axisVector k)).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change centerParameterDerivative (pairHessian (axisVector k)) v +
    centerStateHessian 20 (pairHessian (axisVector k)) 0 = _
  simp [centerParameterDerivative_axisVector]

end Problem356.GeometryJets

end

end OAI
