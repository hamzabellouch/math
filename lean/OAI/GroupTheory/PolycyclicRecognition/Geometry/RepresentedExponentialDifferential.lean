import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialDuhamelDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularOperatorAverage
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation

namespace OAI

/-! # The exponential differential in a faithful Lie representation

Left translation identifies this differential with the average of the
negative adjoint flow. A real triangular adjoint basis makes that average
invertible, independently of a global exponential chart.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance : NormedAddCommGroup L := generatorConjugationNormedAddCommGroup
local instance : NormedSpace ℝ L := generatorConjugationNormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem represented_exponential_differential
    (j : L →ₗ⁅ℝ⁆ A) (x v : L) :
    fderiv ℝ NormedSpace.exp (j x) (j v) =
      NormedSpace.exp (j x) * j
        (operatorExpAverage (-(continuousAd x)) v) := by
  let D : L →L[ℝ] L := continuousAd x
  let J : L →L[ℝ] A := j.toLinearMap.toContinuousLinearMap
  let F : (L →L[ℝ] L) →L[ℝ] A :=
    ((ContinuousLinearMap.mul ℝ A (NormedSpace.exp (j x))).comp J).comp
      (ContinuousLinearMap.apply ℝ L v)
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have he (t : ℝ) : j (NormedSpace.exp (t • (-D)) v) =
      NormedSpace.exp (-(t • j x)) * j v * NormedSpace.exp (t • j x) := by
    have h := exp_intertwine_apply J (t • (-D)) ((-t) • adjointOperator (j x))
      (fun w => by
        change j (t • -⁅x, w⁆) = (-t) • (j x * j w - j w * j x)
        rw [map_smul, map_neg, j.map_lie]
        simp only [neg_smul, smul_neg]
        rfl) v
    rw [exp_smul_adjointOperator_apply] at h
    change j (NormedSpace.exp (t • (-D)) v) =
      NormedSpace.exp ((-t) • j x) * j v * NormedSpace.exp (-((-t) • j x)) at h
    simpa only [neg_smul, neg_neg] using h
  have hprod (t : ℝ) :
      NormedSpace.exp (j x) * NormedSpace.exp (-(t • j x)) =
        NormedSpace.exp ((1 - t) • j x) := by
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl (j x)).smul_right t).neg_right]
    congr 1
    rw [sub_smul, one_smul, sub_eq_add_neg]
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • (-D))) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  rw [fderiv_exp_eq_integral]
  change _ = F (∫ t in (0 : ℝ)..1, NormedSpace.exp (t • (-D)))
  rw [← F.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 1)]
  apply intervalIntegral.integral_congr
  intro t _
  change _ = NormedSpace.exp (j x) * j (NormedSpace.exp (t • (-D)) v)
  rw [he, ← mul_assoc, ← mul_assoc, hprod]

theorem represented_exponential_differential_injective
    {n : ℕ} (T : TriangularAdjoint L n) (j : L →ₗ⁅ℝ⁆ A)
    (hj : Function.Injective j) (x : L) :
    Function.Injective ((fderiv ℝ NormedSpace.exp (j x)).comp
      j.toLinearMap.toContinuousLinearMap) := by
  let D : L →L[ℝ] L := continuousAd x
  have hu : (LinearMap.toMatrix T.basis T.basis (-D).toLinearMap).IsUpperTriangular := by
    change (LinearMap.toMatrix T.basis T.basis (-LieAlgebra.ad ℝ L x)).IsUpperTriangular
    rw [map_neg]
    intro i k hki
    simp only [Matrix.neg_apply, T.upper x hki, neg_zero]
  have hQ := operatorExpAverage_injective T.basis (-D) hu
  intro v w h
  change fderiv ℝ NormedSpace.exp (j x) (j v) =
    fderiv ℝ NormedSpace.exp (j x) (j w) at h
  rw [represented_exponential_differential, represented_exponential_differential] at h
  exact hQ (hj ((NormedSpace.isUnit_exp (j x)).mul_left_cancel h))

end PolycyclicRecognition

end

end OAI
