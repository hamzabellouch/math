import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDecomposition
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.DirectSum.LinearMap

namespace OAI

/-! # Cartan roots descend to and separate canonical height

The roots vanish on the canonical nilpotent kernel. Conversely, vanishing of
all nonzero roots forces zero canonical height. Thus the weight coordinates
used by the box estimates are coordinates on the actual canonical quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

omit [FiniteDimensional ℝ L] in
theorem cartan_weight_zero_of_height_zero (χ : Weight ℝ H L) (h : H)
    (hh : heightProjection T.character h = 0) : χ h = 0 := by
  apply χ.apply_eq_zero_of_isNilpotent h
  apply T.ad_nilpotent_of_mem_kernel
  exact (Submodule.Quotient.mk_eq_zero _).mp hh

theorem cartan_ad_nilpotent_of_weights_zero (T : TriangularAdjoint L n)
    (h : H) (hh : ∀ χ : Weight ℝ H L, χ h = 0) :
    _root_.IsNilpotent (LieAlgebra.ad ℝ L h) := by
  let := T.isTriangularizable
  have ht : genWeightSpaceOf L (0 : ℝ) h = ⊤ := by
    apply top_unique
    rw [← iSup_genWeightSpace_eq_top' ℝ H L]
    apply iSup_le
    intro χ
    simpa only [hh χ] using genWeightSpace_le_genWeightSpaceOf L h (χ : H → ℝ)
  have hk := congrArg LieSubmodule.toSubmodule ht
  change (LieAlgebra.ad ℝ L h).maxGenEigenspace 0 = ⊤ at hk
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.genEigenspace_nat, zero_smul, sub_zero, LinearMap.ker_eq_top] at hk
  exact ⟨Module.finrank ℝ L, hk⟩

/-- Choose a linear Cartan representative of each height. -/
def cartanHeightSection : HeightSpace T.character →ₗ[ℝ] H :=
  Classical.choose (((heightProjection T.character).comp H.subtype).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cartan_height_surjective T H)))

@[simp] theorem cartanHeightSection_height (w : HeightSpace T.character) :
    heightProjection T.character (cartanHeightSection T H w : L) = w := by
  have hs := Classical.choose_spec (((heightProjection T.character).comp H.subtype).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cartan_height_surjective T H)))
  exact congrArg (fun f : HeightSpace T.character →ₗ[ℝ] HeightSpace T.character => f w) hs

/-- A Cartan root as a linear form on the canonical height quotient. -/
def cartanHeightWeight (χ : Weight ℝ H L) : HeightSpace T.character →ₗ[ℝ] ℝ :=
  (χ : H →ₗ[ℝ] ℝ).comp (cartanHeightSection T H)

@[simp] theorem cartanHeightWeight_projection (χ : Weight ℝ H L) (h : H) :
    cartanHeightWeight T H χ (heightProjection T.character h) = χ h := by
  have hz : heightProjection T.character
      ((cartanHeightSection T H (heightProjection T.character h) - h : H) : L) = 0 := by
    change heightProjection T.character
      ((cartanHeightSection T H (heightProjection T.character h) : L) - h) = 0
    rw [map_sub, cartanHeightSection_height, sub_self]
  have hc := cartan_weight_zero_of_height_zero T H χ _ hz
  change χ (cartanHeightSection T H (heightProjection T.character h) - h) = 0 at hc
  rw [map_sub, sub_eq_zero] at hc
  exact hc

/-- The finite family of nonzero Cartan roots separates canonical height. -/
theorem cartanHeightWeights_separate (w : HeightSpace T.character)
    (hw : ∀ χ : Weight ℝ H L, χ.IsNonZero → cartanHeightWeight T H χ w = 0) : w = 0 := by
  let h := cartanHeightSection T H w
  have hz (χ : Weight ℝ H L) : χ h = 0 := by
    by_cases hχ : χ.IsNonZero
    · exact hw χ hχ
    · have hχ' : (χ : H → ℝ) = 0 := not_not.mp hχ
      exact congrFun hχ' h
  have hk := T.mem_kernelIdeal_of_ad_nilpotent h
    (cartan_ad_nilpotent_of_weights_zero (T := T) (H := H) h hz)
  have hp := (Submodule.Quotient.mk_eq_zero _).mpr hk
  change heightProjection T.character (h : L) = 0 at hp
  simpa only [h, cartanHeightSection_height] using hp

/-- The trace of the adjoint action is the dimension-weighted sum of the
actual Cartan roots, including their nonsemisimple parts. -/
theorem trace_ad_eq_sum_cartan_roots (T : TriangularAdjoint L n) (h : H) :
    LinearMap.trace ℝ L (LieAlgebra.ad ℝ L h) =
      ∑ χ : Weight ℝ H L, Module.finrank ℝ (rootSpace H χ) • χ h := by
  classical
  let := T.isTriangularizable
  have hstable (χ : Weight ℝ H L) : Set.MapsTo (LieAlgebra.ad ℝ L h)
      (rootSpace H χ) (rootSpace H χ) := fun v hv => (rootSpace H χ).lie_mem hv
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℝ H L))
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℝ H L))
  rw [LinearMap.trace_eq_sum_trace_restrict hds hstable]
  apply Finset.sum_congr rfl
  intro χ _
  exact trace_toEnd_genWeightSpace ℝ H L (χ : H → ℝ) h

/-- Unimodularity supplies the balancing relation on the canonical quotient. -/
theorem balanced_cartanHeightWeights
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
    (w : HeightSpace T.character) :
    ∑ χ : Weight ℝ H L,
      (Module.finrank ℝ (rootSpace H χ) : ℝ) * cartanHeightWeight T H χ w = 0 := by
  have ht := (trace_ad_eq_sum_cartan_roots (T := T) (H := H)
    (cartanHeightSection T H w)).symm.trans (hunimod _)
  simpa only [nsmul_eq_mul, cartanHeightWeight, LinearMap.comp_apply,
    Weight.toLinear_apply] using ht

end PolycyclicRecognition

end

end OAI
