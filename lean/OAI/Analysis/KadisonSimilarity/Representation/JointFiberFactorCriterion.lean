import OAI.Analysis.KadisonSimilarity.Representation.GlobalFiberRestriction
import OAI.Analysis.KadisonSimilarity.Representation.RepresentationCenterTransport
import OAI.Analysis.KadisonSimilarity.Representation.JointRankOneFactors
import OAI.Analysis.KadisonSimilarity.Representation.ProjectionCentralData

namespace OAI

/-! Countably many rank-one members of joint fibers imply scalar centers
for the restricted source, on any measurable base. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

variable {A F Ω : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace Ω]

theorem ae_joint_fiber_scalar_center
    (B C : StarSubalgebra ℂ A) [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (μ : Measure Ω) (s : Set Ω)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ] (F →L[ℂ] F))
    (d : ℕ → F) (hd : DenseRange d)
    (hRank : ∀ i j : ℕ, ∀ᵐ x ∂μ,
      InnerProductSpace.rankOne ℂ
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) (d i))
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) (d j)) ∈
        representationVonNeumannAlgebra
          (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x))) :
    ∀ᵐ x ∂μ,
      ∀ a : (representationVonNeumannAlgebra (nonunitalRangeRepresentation
        (zeroExtendNonunitalRepresentation s
          (fun y => unitizationRestrict
            (StarSubalgebra.inclusion (le_jointCStarSource_left B C)) (ρ y)) x))).toStarSubalgebra,
        (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  let φ := StarSubalgebra.inclusion (le_jointCStarSource_left B C)
  let τ := zeroExtendNonunitalRepresentation s ρ
  let p := fun x => nonunitalUnitProjection (τ x)
  let hp := fun x => nonunitalUnitProjection_isStarProjection (τ x)
  have hall := eventually_countable_forall.mpr fun i =>
    eventually_countable_forall.mpr fun j => hRank i j
  filter_upwards [hall] with x hx
  have hscalar := joint_first_scalar_center_of_rankOne B C hBC
    (nonunitalRangeRepresentation (τ x))
    (fun i => projectionFiberRetraction (p x) (hp x) (d i))
    (projectionFiber_denseRange d hd (p x) (hp x)) hx
  apply scalar_center_of_representation_equiv
    (globalRestrictionFiberEquiv s φ ρ x).conjStarAlgEquiv
    _ ((nonunitalRangeRepresentation (τ x)).comp φ) _ hscalar
  intro b
  exact congrArg (fun f => f b) (globalRestriction_range_conjugacy s φ ρ x)

end KadisonSimilarity

end

end OAI
