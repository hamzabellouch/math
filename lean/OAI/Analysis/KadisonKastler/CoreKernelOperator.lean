import OAI.Analysis.KadisonKastler.ScalarOperatorKernel
import OAI.Analysis.KadisonKastler.RationalCoreExtension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Algebra.Module.LinearMap.Rat

namespace OAI

/-! # Reconstruction of a bounded operator from a coherent core kernel

Riesz representation first reconstructs the image of every vector in the
countable rational core. The complex-linear extension preserves the bound.
-/

namespace KadisonKastler

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance coreKernelRationalNormedSpace : NormedSpace ℚ H :=
  NormedSpace.restrictScalars ℚ ℂ H

namespace ScalarOperatorKernel.CoherentCore

variable {K : ScalarOperatorKernel H μ} {C : RationalComplexCore H}
  {k : C.space → C.space → ℂ} (hk : K.CoherentCore C k)

/-- Conjugating the test-vector slot makes it rational-linear. -/
def conjugateFunctional (ξ : C.space) : C.space →ₗ[ℚ] ℂ :=
  ({ toFun := fun η => star (k ξ η)
     map_zero' := by
       have hz : k ξ 0 = 0 := by
         simpa only [zero_smul, Rat.cast_zero, zero_mul] using hk.rat_right 0 ξ 0
       rw [hz, star_zero]
     map_add' := fun η ζ => by rw [hk.add_right, star_add] } : C.space →+ ℂ).toRatLinearMap

theorem conjugateFunctional_bound (ξ η : C.space) :
    ‖hk.conjugateFunctional ξ η‖ ≤ (K.bound * ‖ξ‖) * ‖(η : H)‖ := by
  change ‖star (k ξ η)‖ ≤ (K.bound * ‖ξ‖) * ‖(η : H)‖
  simpa only [norm_star, Submodule.norm_coe] using hk.bound ξ η

theorem conjugateFunctional_mulI (ξ η : C.space) :
    hk.conjugateFunctional ξ (C.mulI η) =
      Complex.I • hk.conjugateFunctional ξ η := by
  change star (k ξ (C.mulI η)) = Complex.I * star (k ξ η)
  rw [hk.I_right, star_mul]
  simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, mul_comm]

/-- The continuous scalar functional associated with a core input. -/
def extendedFunctional (ξ : C.space) : H →L[ℂ] ℂ :=
  C.extendComplex (hk.conjugateFunctional ξ) (hk.conjugateFunctional_bound ξ)
    (hk.conjugateFunctional_mulI ξ)

@[simp]
theorem extendedFunctional_coe (ξ η : C.space) :
    hk.extendedFunctional ξ (η : H) = star (k ξ η) :=
  C.extendComplex_coe _ _ _ η

variable [CompleteSpace H]

/-- Riesz representation supplies the image of a core vector. -/
def coreVector (ξ : C.space) : H :=
  (InnerProductSpace.toDual ℂ H).symm (hk.extendedFunctional ξ)

theorem coreVector_inner (ξ η : C.space) :
    inner ℂ (η : H) (hk.coreVector ξ) = k ξ η := by
  calc
    inner ℂ (η : H) (hk.coreVector ξ) =
        star (inner ℂ (hk.coreVector ξ) (η : H)) :=
      (inner_conj_symm (η : H) (hk.coreVector ξ)).symm
    _ = star (hk.extendedFunctional ξ (η : H)) := by
      rw [coreVector, InnerProductSpace.toDual_symm_apply]
    _ = k ξ η := by rw [hk.extendedFunctional_coe, star_star]

theorem coreVector_bound (ξ : C.space) :
    ‖hk.coreVector ξ‖ ≤ K.bound * ‖(ξ : H)‖ := by
  rw [coreVector, (InnerProductSpace.toDual ℂ H).symm.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg K.bound_nonneg (norm_nonneg _)
  · exact C.norm_extendComplex_le _ (hk.conjugateFunctional_bound ξ)
      (hk.conjugateFunctional_mulI ξ)

theorem coreVector_add (ξ ζ : C.space) :
    hk.coreVector (ξ + ζ) = hk.coreVector ξ + hk.coreVector ζ := by
  apply C.dense.eq_of_inner_right ℂ
  intro η hη
  let η' : C.space := ⟨η, hη⟩
  change inner ℂ (η' : H) _ = inner ℂ (η' : H) _
  rw [inner_add_right, hk.coreVector_inner, hk.coreVector_inner, hk.coreVector_inner,
    hk.add_left]

theorem coreVector_rat_smul (r : ℚ) (ξ : C.space) :
    hk.coreVector (r • ξ) = r • hk.coreVector ξ := by
  apply C.dense.eq_of_inner_right ℂ
  intro η hη
  let η' : C.space := ⟨η, hη⟩
  change inner ℂ (η' : H) _ = inner ℂ (η' : H) _
  have hs : r • hk.coreVector ξ = (r : ℂ) • hk.coreVector ξ := by
    simpa only [Rat.cast_id] using ratCast_smul_eq ℚ ℂ r (hk.coreVector ξ)
  rw [hs, inner_smul_right,
    hk.coreVector_inner, hk.coreVector_inner, hk.rat_left]

theorem coreVector_mulI (ξ : C.space) :
    hk.coreVector (C.mulI ξ) = Complex.I • hk.coreVector ξ := by
  apply C.dense.eq_of_inner_right ℂ
  intro η hη
  let η' : C.space := ⟨η, hη⟩
  change inner ℂ (η' : H) _ = inner ℂ (η' : H) _
  rw [inner_smul_right, hk.coreVector_inner, hk.coreVector_inner, hk.I_left]

/-- The Riesz images form a rational-linear map on the core. -/
def coreLinearMap : C.space →ₗ[ℚ] H where
  toFun := hk.coreVector
  map_add' := hk.coreVector_add
  map_smul' := hk.coreVector_rat_smul

theorem coreLinearMap_bound (ξ : C.space) :
    ‖hk.coreLinearMap ξ‖ ≤ K.bound * ‖(ξ : H)‖ := hk.coreVector_bound ξ

theorem coreLinearMap_mulI (ξ : C.space) :
    hk.coreLinearMap (C.mulI ξ) = Complex.I • hk.coreLinearMap ξ := hk.coreVector_mulI ξ

/-- The bounded complex-linear operator reconstructed from the kernel. -/
def toOperator : H →L[ℂ] H :=
  C.extendComplex hk.coreLinearMap hk.coreLinearMap_bound hk.coreLinearMap_mulI

theorem toOperator_norm_le : ‖hk.toOperator‖ ≤ K.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ K.bound_nonneg
  exact C.norm_extendComplex_le hk.coreLinearMap hk.coreLinearMap_bound hk.coreLinearMap_mulI

theorem toOperator_inner (ξ η : C.space) :
    inner ℂ (η : H) (hk.toOperator (ξ : H)) = k ξ η := by
  rw [toOperator, C.extendComplex_coe]
  exact hk.coreVector_inner ξ η

/-- The core matrix coefficients uniquely determine the reconstructed operator. -/
theorem eq_toOperator (T : H →L[ℂ] H)
    (hT : ∀ ξ η : C.space, inner ℂ (η : H) (T (ξ : H)) = k ξ η) :
    T = hk.toOperator := by
  have h : (T : H → H) = hk.toOperator := by
    apply C.dense.denseRange_val.equalizer T.continuous hk.toOperator.continuous
    funext ξ
    apply C.dense.eq_of_inner_right ℂ
    intro η hη
    exact (hT ξ ⟨η, hη⟩).trans (hk.toOperator_inner ξ ⟨η, hη⟩).symm
  exact DFunLike.coe_injective h

include hk

/-- A coherent scalar core kernel is represented by an operator with the
same bound; no measurable selection is involved in this construction. -/
theorem exists_operator :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ K.bound ∧
      ∀ ξ η : C.space, inner ℂ (η : H) (T (ξ : H)) = k ξ η :=
  ⟨hk.toOperator, hk.toOperator_norm_le, hk.toOperator_inner⟩

end ScalarOperatorKernel.CoherentCore

end

end KadisonKastler

end OAI
