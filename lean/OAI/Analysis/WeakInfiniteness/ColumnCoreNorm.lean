import Mathlib
import OAI.Analysis.WeakInfiniteness.ColumnNormalization

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma norm_column_core (D : B) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖cfc (columnCoreFunction τ) (star D*D)‖=max (‖D‖-τ) 0 := by
  obtain hB | hB := subsingleton_or_nontrivial B
  · have hD : D=0 := Subsingleton.elim _ _
    have hz : cfc (columnCoreFunction τ) (star D*D)=0 := Subsingleton.elim _ _
    rw [hz,norm_zero,hD,norm_zero]
    simp only [zero_sub,max_eq_right (neg_nonpos.mpr hτ)]
  let : Nontrivial B := hB
  apply le_antisymm
  · apply norm_cfc_le (le_max_right _ _)
    intro s hs
    have hs0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs
    have hsn := (Real.le_norm_self s).trans (spectrum.norm_le_norm_of_mem hs)
    rw [CStarRing.norm_star_mul_self] at hsn
    have hsr : Real.sqrt s ≤ ‖D‖ := by
      nlinarith [Real.sq_sqrt hs0,Real.sqrt_nonneg s,norm_nonneg D]
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith) le_rfl
  · have he := norm_apply_le_norm_cfc (columnCoreFunction τ) (star D*D)
      (CStarAlgebra.norm_mem_spectrum_of_nonneg (star D * D) (star_mul_self_nonneg D))
      (continuous_columnCoreFunction τ).continuousOn (IsSelfAdjoint.star_mul_self D)
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),CStarRing.norm_star_mul_self] at he
    simpa only [columnCoreFunction,Real.sqrt_mul_self (norm_nonneg D)] using he

end

end

end WeakPureInfiniteness
end

end OAI
