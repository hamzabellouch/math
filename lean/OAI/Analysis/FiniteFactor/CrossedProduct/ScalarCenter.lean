import OAI.Analysis.FiniteFactor.Model
import OAI.Analysis.FiniteFactor.CrossedProduct.RotationErgodic
import OAI.Analysis.FiniteFactor.CrossedProduct.CentralScalarField

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Constancy of the representing field is equality of the original operators. -/
theorem sourceOperator_eq_scalar_of_field (θ : SourceCoordinate → ℝ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (c : ℂ)
    (hc : ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField A x =
      c • (1 : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)) :
    A = c • (1 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) := by
  apply ContinuousLinearMap.ext
  intro f
  change A f = c • f
  apply Lp.ext
  have he : ∀ᵐ z ∂sourceMeasure SourceCoordinate, (A f) z = c * f z := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (A f)).measurable
        (measurable_const.mul (Lp.stronglyMeasurable f).measurable))).mpr
    filter_upwards [sourceOperatorField_represents θ hA f,sourceFiberVector_coe (A f),
      sourceFiberVector_coe f,hc] with x ha hAf hf hx
    apply Eventually.of_forall
    intro k
    have hk := congrArg (fun v : SourceFiberHilbert => v k) ha
    rw [hx] at hk
    change sourceFiberVector (A f) x k = c * sourceFiberVector f x k at hk
    simpa only [hAf,hf,Pi.mul_apply] using hk
  filter_upwards [he,Lp.coeFn_smul c f] with z hz hs
  simpa only [hs,Pi.smul_apply,smul_eq_mul] using hz

theorem sourceCentralCoefficient_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∃ c : ℂ, sourceCentralCoefficient A =ᵐ[sourceBaseMeasure] fun _ => c := by
  apply sourceRotation_invariant_constant θ hr (sourceCentralCoefficient_measurable A)
  filter_upwards [sourceCentralCoefficient_rotation_invariant θ hr hA hcentral] with x hx
  exact hx 1

theorem sourceAlgebra_hasScalarCenter (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) : HasScalarCenter (sourceAlgebra θ) := by
  intro A hA hcentral
  obtain ⟨c,hc⟩ := sourceCentralCoefficient_constant θ hr hA hcentral
  refine ⟨c,sourceOperator_eq_scalar_of_field θ hA c ?_⟩
  filter_upwards [sourceCentral_scalar_field θ hr hA hcentral,hc] with x hx hc
  rw [hx,hc]

end
end FiniteFactor

end OAI
