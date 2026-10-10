import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDerivative
import Mathlib.Algebra.Lie.Derivation.Basic

namespace OAI

/-! # The analytic exponential of any finite-dimensional real derivation

Intertwining the bracket with the operator commutator proves bracket
preservation. The derivation need not be nilpotent.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem derivation_bracket_intertwine (D : LieDerivation ℝ L L) (x : L) :
    normedLieBracket (D x) =
      adjointOperator (LinearMap.toContinuousLinearMap D.toLinearMap) (normedLieBracket x) := by
  apply ContinuousLinearMap.ext
  intro y
  change ⁅D x, y⁆ = D ⁅x, y⁆ - ⁅x, D y⁆
  rw [D.apply_lie_eq_sub]
  have h := lie_skew (D x) y
  rw [← h]
  abel

theorem analytic_derivation_exp_preserves_lie (D : LieDerivation ℝ L L) (x y : L) :
    NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) ⁅x, y⁆ =
      ⁅NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) x,
        NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) y⁆ := by
  let d := LinearMap.toContinuousLinearMap D.toLinearMap
  have h := exp_intertwine_apply (normedLieBracket (L := L)) d (adjointOperator d)
    (derivation_bracket_intertwine D) x
  rw [exp_adjointOperator_apply] at h
  have hi := congrArg (fun T : L →L[ℝ] L => T y) (algebraExpUnit d).inv_val
  change NormedSpace.exp (-d) (NormedSpace.exp d y) = y at hi
  have he := DFunLike.congr_fun h (NormedSpace.exp d y)
  change ⁅NormedSpace.exp d x, NormedSpace.exp d y⁆ =
    NormedSpace.exp d ⁅x, NormedSpace.exp (-d) (NormedSpace.exp d y)⁆ at he
  rw [hi] at he
  exact he.symm

def analyticDerivationExp (D : LieDerivation ℝ L L) : L ≃ₗ⁅ℝ⁆ L :=
  { (ContinuousLinearEquiv.ofUnit
      (algebraExpUnit (LinearMap.toContinuousLinearMap D.toLinearMap))).toLinearEquiv with
    map_lie' := fun {x y} => analytic_derivation_exp_preserves_lie D x y }

@[simp] theorem analyticDerivationExp_apply (D : LieDerivation ℝ L L) (x : L) :
    analyticDerivationExp D x =
      NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) x := rfl

def analyticDerivationFlow (D : LieDerivation ℝ L L) (t : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  analyticDerivationExp (t • D)

theorem analyticDerivationFlow_zero (D : LieDerivation ℝ L L) (x : L) :
    analyticDerivationFlow D 0 x = x := by
  rw [analyticDerivationFlow, zero_smul, analyticDerivationExp_apply]
  change NormedSpace.exp (0 : L →L[ℝ] L) x = x
  rw [NormedSpace.exp_zero]
  rfl

theorem analyticDerivationFlow_add (D : LieDerivation ℝ L L) (s t : ℝ) (x : L) :
    analyticDerivationFlow D (s + t) x =
      analyticDerivationFlow D s (analyticDerivationFlow D t x) := by
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let d := LinearMap.toContinuousLinearMap D.toLinearMap
  change NormedSpace.exp ((s + t) • d) x =
    NormedSpace.exp (s • d) (NormedSpace.exp (t • d) x)
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl d).smul_left s).smul_right t)]
  rfl

end PolycyclicRecognition

end

end OAI
