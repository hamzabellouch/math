import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootFlow
import Mathlib.LinearAlgebra.Eigenspace.Zero

namespace OAI

/-! # Polynomial bounds for the residual Cartan action

On an actual generalized root space, subtracting its scalar character leaves
an operator nilpotent in a uniform dimension bound. Its exponential therefore
has polynomial growth in the Cartan parameter. This supplies the residual
operator estimate used in box conjugation.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module

/-- Split an arbitrary scalar character from an operator exponential. -/
theorem exp_eq_scalar_smul_residual
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (X : A) :
    NormedSpace.exp X = Real.exp a • NormedSpace.exp (X - a • 1) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute (a • (1 : A)) (X - a • 1) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_left a (X - a • 1)
  have he : NormedSpace.exp (a • (1 : A)) = Real.exp a • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) a).symm
  conv_lhs => rw [show X = a • 1 + (X - a • 1) by module]
  rw [NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

local instance : NormedAddCommGroup (rootSpace H χ) :=
  NormedAddCommGroup.induced _ _ (rootCoordinates H χ).toLinearMap
    (rootCoordinates H χ).injective
local instance : NormedSpace ℝ (rootSpace H χ) :=
  NormedSpace.induced ℝ _ _ (rootCoordinates H χ).toLinearMap
local instance : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot

/-- The nilpotence exponent is uniformly bounded by the root-space dimension. -/
theorem rootAction_residual_pow_eq_zero (h : H) :
    (rootAction H χ h - χ h • 1) ^ finrank ℝ (rootSpace H χ) = 0 := by
  let A : Module.End ℝ (rootSpace H χ) := toEnd ℝ H (rootSpace H χ) h - χ h • 1
  have hn : _root_.IsNilpotent A := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  have hp : A ^ finrank ℝ (rootSpace H χ) = 0 := by
    simpa only [hn.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X] using
      A.aeval_self_charpoly
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hp
  simpa only [A, map_pow, map_sub, map_smul, map_one, map_zero, rootAction] using hm

/-- Dependence of the residual operator on the Cartan parameter is linear. -/
def rootResidualLinear : H →ₗ[ℝ] ((rootSpace H χ) →L[ℝ] (rootSpace H χ)) where
  toFun h := rootAction H χ h - χ h • 1
  map_add' h k := by
    change Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)
      (toEnd ℝ H (rootSpace H χ) (h + k)) - χ (h + k) • 1 = _
    simp only [map_add, add_smul, rootAction]
    abel
  map_smul' a h := by
    change Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)
      (toEnd ℝ H (rootSpace H χ) (a • h)) - χ (a • h) • 1 = _
    simp only [map_smul, smul_sub, smul_smul, RingHom.id_apply]
    rfl

/-- One polynomial controls the residual operator for every Cartan parameter. -/
theorem exists_rootResidual_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h : H,
      ‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) := by
  let d := finrank ℝ (rootSpace H χ)
  let b := Module.finBasis ℝ H
  let f := ((rootResidualLinear H χ).comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
  let K := ‖f‖
  have hK : 0 ≤ K := norm_nonneg f
  refine ⟨((d : ℝ) + 1) * (1 + K) ^ d * 2 ^ d, by positivity, ?_⟩
  intro h
  have hb : ‖rootAction H χ h - χ h • 1‖ ≤ K * ‖(Module.finBasis ℝ H).equivFun h‖ := by
    have hf : f (b.equivFun h) = rootAction H χ h - χ h • 1 := by
      change rootResidualLinear H χ (b.equivFun.symm (b.equivFun h)) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    simpa only [hf] using f.le_opNorm (b.equivFun h)
  have hp : (rootAction H χ h - χ h • 1) ^ (d + 1) = 0 := by
    rw [pow_succ, rootAction_residual_pow_eq_zero, zero_mul]
  have he := norm_exp_smul_nilpotent_le (rootAction H χ h - χ h • 1) hp (t := 1) zero_le_one
  simp only [one_smul, one_add_one_eq_two] at he
  calc
    _ ≤ ((d : ℝ) + 1) * (1 + ‖rootAction H χ h - χ h • 1‖) ^ d * 2 ^ d := he
    _ ≤ ((d : ℝ) + 1) * ((1 + K) * (1 + ‖(Module.finBasis ℝ H).equivFun h‖)) ^ d * 2 ^ d := by
      gcongr
      nlinarith [norm_nonneg (b.equivFun h)]
    _ = _ := by rw [mul_pow]; ring

/-- Restoring the scalar character gives the full root action estimate. -/
theorem exists_rootAction_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : H) (v : rootSpace H χ),
      ‖(NormedSpace.exp (rootAction H χ h)) v‖ ≤
        C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) * Real.exp (χ h) * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_rootResidual_exp_bound H χ
  refine ⟨C, hC, fun h v => ?_⟩
  rw [exp_eq_scalar_smul_residual (χ h) (rootAction H χ h),
    smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (χ h) *
        (‖NormedSpace.exp (rootAction H χ h - χ h • 1)‖ * ‖v‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (χ h) *
        (C * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ finrank ℝ (rootSpace H χ) * ‖v‖) := by
      gcongr
      exact hbound h
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
