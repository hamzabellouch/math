import OAI.Analysis.KadisonSimilarity.Representation.ProjectionCentralData
import OAI.Analysis.KadisonSimilarity.Representation.SupportedFieldRecovery

namespace OAI

/-! Abstract isometric compression supplies supported rank-one members of
the actual fiber bicommutants. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {Ω F H B : Type u} [MeasurableSpace Ω] [CStarAlgebra B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem ae_supported_projection_rankOne_mem (μ : Measure Ω) [IsFiniteMeasure μ]
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (hcompression : ∀ (R : Ω → F →L[ℂ] F)
      (hm : ∀ z, AEStronglyMeasurable (fun x => R x z) μ)
      (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ C),
      ((J.toContinuousLinearMap.adjoint.comp (boundedFieldOperator μ R hm C hb)).comp
        J.toContinuousLinearMap) ∈ representationVonNeumannAlgebra σ)
    (v w : F) :
    ∀ᵐ x ∂μ, InnerProductSpace.rankOne ℂ
      (projectionFiberRetraction
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) v)
      (projectionFiberRetraction
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) w) ∈
      representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  let p := fun x => nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x)
  have hp (x) : IsStarProjection (p x) :=
    nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)
  have hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J 1 f x = p x (f x) := by
    intro f
    have h := zeroExtendOperatorField_action μ s hs hnull
      (isometricExtension J (σ 1)) (fun x => ρ x (Unitization.inr 1)) (hρ 1) f
    simpa only [map_one, zeroExtendNonunitalRepresentation_apply, nonunitalUnitProjection,
      p] using h
  let R := fun x => InnerProductSpace.rankOne ℂ (p x v) (p x w)
  have hm : ∀ z, AEStronglyMeasurable (fun x => R x z) μ :=
    aestronglyMeasurable_projection_rankOne μ p
      (aestronglyMeasurable_isometric_projection_column μ J p hP) v w
  have hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ ‖v‖ * ‖w‖ :=
    Eventually.of_forall fun x => norm_projection_rankOne_le (p x) (hp x) v w
  let Q := boundedFieldOperator μ R hm (‖v‖ * ‖w‖) hb
  let T := (J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap
  have hT : T ∈ representationVonNeumannAlgebra σ := hcompression R hm _ hb
  have he : isometricExtension J T = Q :=
    isometricExtension_boundedField_compression μ J p R hP hm _ hb
      (Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).1)
      (Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).2)
  have haction : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J T f x = R x (f x) := by
    intro f
    rw [he]
    exact boundedFieldOperator_action μ R hm _ hb f
  have hmem := ae_global_projection_mem_of_isometric_closure μ s hs hnull J σ ρ hρ
    T hT R haction
  filter_upwards [hmem] with x hx
  change projectionFiberCompression (p x) (hp x)
    (InnerProductSpace.rankOne ℂ (p x v) (p x w)) ∈ _ at hx
  rw [projectionFiberCompression_rankOne] at hx
  exact hx

end KadisonSimilarity

end

end OAI
