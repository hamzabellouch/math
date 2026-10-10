import OAI.Analysis.KadisonKastler.CoreKernelOperator
import OAI.Analysis.KadisonKastler.WeakOperatorCoefficients

namespace OAI

/-! # Reconstructing measurable operator fields from scalar kernels

The coherent countable-core representatives give pointwise bounded
operators. Dense scalar tests prove measurability; continuity of the
L-infinity kernel then identifies all coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ScalarOperatorKernel

variable (K : ScalarOperatorKernel H μ) (C : RationalComplexCore H)

/-- The scalar kernel gives a bounded operator at every good point,
and zero on the exceptional null set. -/
def reconstructedOperator (x : D) : H →L[ℂ] H := by
  classical
  exact if h : K.CoherentCore C (fun ξ η => K.coeff (ξ : H) (η : H) x) then h.toOperator else 0

theorem reconstructedOperator_norm_le (x : D) : ‖K.reconstructedOperator C x‖ ≤ K.bound := by
  unfold reconstructedOperator
  split_ifs with h
  · exact h.toOperator_norm_le
  · simpa only [norm_zero] using K.bound_nonneg

/-- Every countable-core matrix coefficient is the supplied scalar representative. -/
theorem reconstructedOperator_core_ae (ξ η : C.space) :
    ∀ᵐ x ∂μ, inner ℂ (η : H) (K.reconstructedOperator C x (ξ : H)) = K.coeff ξ η x := by
  filter_upwards [K.coherentCore_ae C] with x hx
  simpa only [reconstructedOperator, dite_eq_left hx] using hx.toOperator_inner ξ η

variable [SeparableSpace H]

/-- The resulting field and its adjoint have all strongly measurable evaluations. -/
theorem reconstructedOperator_measurable :
    ∀ ξ : H, AEStronglyMeasurable (fun x => K.reconstructedOperator C x ξ) μ ∧
      AEStronglyMeasurable (fun x => star (K.reconstructedOperator C x) ξ) μ := by
  let : Countable C.space := C.countable
  have hd : DenseRange ((↑) : C.space → H) := C.dense.denseRange_val
  apply operator_field_aestronglyMeasurable_of_dense_coefficients
    ((↑) : C.space → H) hd (K.reconstructedOperator C)
  intro η ξ
  exact (Lp.aestronglyMeasurable (K.coeff ξ η)).congr
    ((K.reconstructedOperator_core_ae C ξ η).mono (fun _ h => h.symm))

/-- A bounded measurable representative reconstructed from the scalar kernel. -/
def reconstructedRepresentative : WeakOperatorRepresentative (H := H) μ :=
  WeakOperatorRepresentative.mk (K.reconstructedOperator C) K.bound
    (K.reconstructedOperator_norm_le C)
    (fun ξ => (K.reconstructedOperator_measurable C ξ).1)
    (fun ξ => (K.reconstructedOperator_measurable C ξ).2)

theorem reconstructedRepresentative_norm_le : ‖K.reconstructedRepresentative C‖ ≤ K.bound :=
  WeakOperatorRepresentative.norm_mk_le _ K.bound_nonneg _ _ _

variable [IsFiniteMeasure μ]

/-- Equality on the core extends to equality of all L-infinity coefficients. -/
theorem reconstructedRepresentative_coefficient (ξ η : H) :
    WeakOperatorRepresentative.coefficient (K.reconstructedRepresentative C) ξ η = K.coeff ξ η := by
  symm
  apply K.coeff_eq_of_core
    (WeakOperatorRepresentative.scalarKernel (K.reconstructedRepresentative C)) C
  intro u v
  apply Lp.ext
  filter_upwards [K.reconstructedOperator_core_ae C u v,
    WeakOperatorRepresentative.coefficient_ae (K.reconstructedRepresentative C) u v] with x hK hR
  exact hK.symm.trans hR.symm

/-- Bounded scalar sesquilinear kernels have actual measurable operator
representatives, with no additional existence premise. -/
theorem exists_representative : ∃ F : WeakOperatorRepresentative (H := H) μ,
    ‖F‖ ≤ K.bound ∧ ∀ ξ η : H, WeakOperatorRepresentative.coefficient F ξ η = K.coeff ξ η := by
  let C : RationalComplexCore H := Classical.choice (exists_rationalComplexCore H)
  exact ⟨K.reconstructedRepresentative C, K.reconstructedRepresentative_norm_le C,
    K.reconstructedRepresentative_coefficient C⟩

end ScalarOperatorKernel

end

end KadisonKastler

end OAI
