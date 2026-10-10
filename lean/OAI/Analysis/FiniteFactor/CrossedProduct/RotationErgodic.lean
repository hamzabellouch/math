import OAI.Analysis.FiniteFactor.CrossedProduct.TorusErgodic

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceTorusRepresentative_rotationStep (θ : SourceCoordinate → ℝ) (z : SourceTorus) :
    sourceTorusRepresentative (sourceTorusRotationStep θ z) =
      coordinateRotate θ 1 (sourceTorusRepresentative z) := by
  funext i
  have hz : ((sourceTorusRepresentative z i : ℝ) : UnitAddCircle) = z i :=
    congrFun (sourceTorusQuotient_representative z) i
  change sourceCircleRepresentative (z i + (θ i : UnitAddCircle)) =
    Int.fract (sourceTorusRepresentative z i + (1 : ℤ) * θ i)
  rw [← hz,← AddCircle.coe_add,sourceCircleRepresentative_coe]
  norm_num

/-- Ergodicity for the exact real-coordinate model used by the original algebra. -/
theorem coordinateRotate_ergodic (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) :
    Ergodic (coordinateRotate θ 1) sourceSamplingHaar :=
  sourceTorusRepresentative_preserving.ergodic_of_ergodic_semiconj
    (sourceTorusRotationStep_ergodic θ hr) (coordinateRotate_preserving θ 1).measurable
    (sourceTorusRepresentative_rotationStep θ)

theorem sourceRotation_invariant_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) {f : (SourceCoordinate → ℝ) → ℂ}
    (hf : Measurable f) (hi : f ∘ coordinateRotate θ 1 =ᵐ[sourceSamplingHaar] f) :
    ∃ c : ℂ, f =ᵐ[sourceSamplingHaar] fun _ => c :=
  (coordinateRotate_ergodic θ hr).ae_eq_const_of_ae_eq_comp₀ hf.nullMeasurable hi

end
end FiniteFactor

end OAI
