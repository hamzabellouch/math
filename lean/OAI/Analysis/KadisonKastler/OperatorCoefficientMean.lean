import OAI.Analysis.KadisonKastler.KernelReconstruction
import OAI.Analysis.KadisonKastler.WeakFieldCoefficients

namespace OAI

/-! # Contractive operator-field averaging from the scalar boundary mean

All objects here are the actual measurable fields modulo almost-everywhere
equality. The construction uses norm-minimizing representatives only to
produce an operator; its scalar coefficients characterize it intrinsically.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace WeakOperatorField

/-- Choose norm-controlled representatives of a bounded operator-field family. -/
def uniformFamily (F : G →ᵇ WeakOperatorField (H := H) μ) :
    UniformMeasurableOperators G D H μ where
  eval g := WeakOperatorRepresentative.eval (representative (F g))
  bound := ‖F‖
  bound_nonneg := norm_nonneg F
  norm_le g x := (WeakOperatorRepresentative.eval_norm_le (representative (F g)) x).trans
    ((norm_representative_le (F g)).trans (F.norm_coe_le_norm g))
  measurable g := WeakOperatorRepresentative.eval_aestronglyMeasurable (representative (F g))

/-- The intrinsic scalar coefficient family. -/
def coefficientFamily (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    G →ᵇ ScalarLInfinity μ := (uniformFamily F).coefficientFamily ξ η

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_apply (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) (g : G) :
    coefficientFamily F ξ η g = coefficient (F g) ξ η := by
  apply Lp.ext
  filter_upwards [(uniformFamily F).coefficient_ae g ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative (F g)) ξ η] with x hF hR
  exact hF.trans hR.symm

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_add (F E : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (F + E) ξ η = coefficientFamily F ξ η + coefficientFamily E ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  simp only [coefficientFamily_apply, BoundedContinuousFunction.add_apply, coefficient_add]

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_smul (c : ℂ) (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (c • F) ξ η = c • coefficientFamily F ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  simp only [coefficientFamily_apply, BoundedContinuousFunction.smul_apply, coefficient_smul]

omit [Group G] [TopologicalSpace.SeparableSpace H] in
theorem coefficientFamily_const (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (BoundedContinuousFunction.const G T) ξ η =
      BoundedContinuousFunction.const G (coefficient T ξ η) := by
  apply BoundedContinuousFunction.ext
  intro g
  exact coefficientFamily_apply _ ξ η g

end WeakOperatorField

variable {α : NonsingularAction G D μ}

namespace ScalarBoundaryMean

variable (m : ScalarBoundaryMean α)

/-- Reconstruct the operator-valued mean from the averaged scalar kernel. -/
def operatorMeanValue (F : G →ᵇ WeakOperatorField (H := H) μ) : WeakOperatorField (H := H) μ :=
  operatorFieldQuotient μ
    (Classical.choose ((WeakOperatorField.uniformFamily F).meanKernel m).exists_representative)

theorem operatorMeanValue_coefficient (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    WeakOperatorField.coefficient (m.operatorMeanValue F) ξ η =
      m.toCLM (WeakOperatorField.coefficientFamily F ξ η) := by
  rw [operatorMeanValue, WeakOperatorField.coefficient_quotient]
  exact (Classical.choose_spec
    ((WeakOperatorField.uniformFamily F).meanKernel m).exists_representative).2 ξ η

theorem norm_operatorMeanValue_le (F : G →ᵇ WeakOperatorField (H := H) μ) :
    ‖m.operatorMeanValue F‖ ≤ ‖F‖ :=
  (operatorFieldQuotient_norm_le μ _).trans (Classical.choose_spec
    ((WeakOperatorField.uniformFamily F).meanKernel m).exists_representative).1

theorem operatorMeanValue_add (F E : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMeanValue (F + E) = m.operatorMeanValue F + m.operatorMeanValue E := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [WeakOperatorField.coefficient_add, m.operatorMeanValue_coefficient,
    m.operatorMeanValue_coefficient, m.operatorMeanValue_coefficient,
    WeakOperatorField.coefficientFamily_add, map_add]

theorem operatorMeanValue_smul (c : ℂ) (F : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMeanValue (c • F) = c • m.operatorMeanValue F := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [WeakOperatorField.coefficient_smul, m.operatorMeanValue_coefficient,
    m.operatorMeanValue_coefficient, WeakOperatorField.coefficientFamily_smul, map_smul]

/-- The scalar boundary mean induces a contractive complex-linear map
on actual essentially bounded measurable operator fields. -/
def operatorMean : (G →ᵇ WeakOperatorField (H := H) μ) →L[ℂ] WeakOperatorField (H := H) μ :=
  LinearMap.mkContinuous
    { toFun := m.operatorMeanValue
      map_add' := m.operatorMeanValue_add
      map_smul' := m.operatorMeanValue_smul }
    1 (fun F => by simpa using m.norm_operatorMeanValue_le F)

@[simp]
theorem operatorMean_apply (F : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMean F = m.operatorMeanValue F := rfl

theorem operatorMean_fixed (T : WeakOperatorField (H := H) μ) :
    m.operatorMean (BoundedContinuousFunction.const G T) = T := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [operatorMean_apply, m.operatorMeanValue_coefficient,
    WeakOperatorField.coefficientFamily_const, m.fixed]

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
