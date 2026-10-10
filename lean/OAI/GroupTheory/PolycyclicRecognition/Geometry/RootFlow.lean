import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGenerators
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentFlow
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Logarithmic distortion in Cartan root spaces

Generalized root spaces determine the nilpotent correction to the scalar
weight action. A compatible group conjugation identity then gives logarithmic
distortion.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

/-- Fixed linear coordinates put a compatible norm on the root space. -/
def rootCoordinates : (rootSpace H χ) ≃ₗ[ℝ]
    (Fin (Module.finrank ℝ (rootSpace H χ)) → ℝ) :=
  (Module.finBasis ℝ (rootSpace H χ)).equivFun

local instance rootNormedAddCommGroup : NormedAddCommGroup (rootSpace H χ) :=
  NormedAddCommGroup.induced _ _ (rootCoordinates H χ).toLinearMap
    (rootCoordinates H χ).injective

local instance rootNormedSpace : NormedSpace ℝ (rootSpace H χ) :=
  NormedSpace.induced ℝ _ _ (rootCoordinates H χ).toLinearMap

local instance rootNontrivial : Nontrivial (rootSpace H χ) :=
  (LieSubmodule.nontrivial_iff_ne_bot ℝ H L).mpr χ.genWeightSpace_ne_bot

/-- The actual adjoint action on a Cartan generalized root space. -/
def rootAction (h : H) : (rootSpace H χ) →L[ℝ] (rootSpace H χ) :=
  Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ) (toEnd ℝ H (rootSpace H χ) h)

theorem rootAction_nilpotent_correction (h : H) :
    _root_.IsNilpotent (rootAction H χ h - χ h • 1) := by
  have hn := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  obtain ⟨k, hk⟩ := hn
  refine ⟨k, ?_⟩
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hk
  simpa only [map_pow, map_sub, Algebra.algebraMap_eq_smul_one,
    map_smul, map_one, map_zero, rootAction] using hm

/-- Each nonzero real root has a direction where its value is `-1`. -/
theorem exists_contracting_root_direction (hχ : χ.IsNonZero) :
    ∃ h : H, χ h = -1 := by
  have hn : ∃ h : H, χ h ≠ 0 := by
    by_contra! hn
    apply hχ
    exact funext hn
  obtain ⟨h, hh⟩ := hn
  refine ⟨(-(χ h)⁻¹) • h, ?_⟩
  rw [map_smul]
  change -(χ h)⁻¹ * χ h = -1
  rw [neg_mul, inv_mul_cancel₀ hh]

/-- Logarithmic distortion follows for an integrated nonzero root chart.
No semisimplicity or diagonal adjoint action is assumed. -/
theorem root_logarithmic_distortion
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • rootAction H χ h)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  let N := rootAction H χ h + 1
  have hnil : _root_.IsNilpotent N := by
    simpa only [hh, neg_smul, one_smul, sub_neg_eq_add, N] using
      rootAction_nilpotent_correction H χ h
  obtain ⟨k, hk⟩ := hnil
  have hk' : N ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  apply logarithmic_distortion_of_weight_generator Exp hExp d hd hd0 hmul N hk'
  simpa only [N, add_sub_cancel_right] using hconj

end PolycyclicRecognition

end

end OAI
