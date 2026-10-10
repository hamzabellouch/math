import OAI.Analysis.KadisonSimilarity.Representation.IsometricFieldClosure
import OAI.Analysis.KadisonSimilarity.Representation.ConullFieldExtension
import OAI.Analysis.KadisonSimilarity.Representation.UnitizationFiberClosure

namespace OAI

/-! # Closure in the genuine projection-fiber algebras

Strong Kaplansky approximation first proves membership in the raw
unitized fiber algebra. Compression to the old-unit range then gives
membership in the genuine representation of the original algebra.
No representation on the null complement is needed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {B H F Ω : Type*} [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The conull raw unitized fiber representations contain the field of
every operator in the original represented bicommutant. -/
theorem ae_unitization_field_mem_of_isometric_closure
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : s → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J T f x = Q x (f x)) :
    ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
      Q x ∈ representationVonNeumannAlgebra (ρ x) := by
  classical
  let P : Ω → VonNeumannAlgebra F := fun x =>
    if hx : x ∈ s then representationVonNeumannAlgebra (ρ ⟨x, hx⟩)
    else starSubalgebraCommutant (⊤ : StarSubalgebra ℂ (F →L[ℂ] F))
  let R : B → Ω → F →L[ℂ] F := fun b =>
    zeroExtendOperatorField s (fun x => ρ x (Unitization.inr b))
  have hR : ∀ b (f : Lp F 2 μ), ∀ᵐ x ∂μ,
      isometricExtension J (σ b) f x = R b x (f x) := fun b =>
    zeroExtendOperatorField_action μ s hs hnull _ _ (hρ b)
  have hmem : ∀ b, ∀ᵐ x ∂μ, R b x ∈ P x := by
    intro b
    apply Filter.Eventually.of_forall
    apply zeroExtendOperatorField_mem s P
    intro x
    simpa only [P, dite_eq_left x.property] using
      mem_representationVonNeumannAlgebra (ρ x) (Unitization.inr b)
  have hQ' : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J T f x = zeroExtendOperatorField s Q x (f x) :=
    zeroExtendOperatorField_action μ s hs hnull _ _ hQ
  have hm := ae_field_mem_of_isometric_representation_closure μ J σ P R hR hmem
    T hT (zeroExtendOperatorField s Q) hQ'
  have hmOn := (ae_restrict_iff_subtype hs).mp (ae_restrict_of_ae hm)
  filter_upwards [hmOn] with x hx
  simpa only [zeroExtendOperatorField, dite_eq_left x.property, P] using hx

/-- Passing to the old-unit range yields membership in the actual
variable-fiber representation of the original algebra. -/
theorem ae_projection_field_mem_of_isometric_closure
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : s → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J T f x = Q x (f x)) :
    ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
      projectionFiberCompression (unitizationProjection (ρ x))
        (unitizationProjection_isStarProjection (ρ x)) (Q x) ∈
          representationVonNeumannAlgebra (unitizationRangeRepresentation (ρ x)) := by
  filter_upwards [ae_unitization_field_mem_of_isometric_closure
    μ s hs hnull J σ ρ hρ T hT Q hQ] with x hx
  exact unitizationFiberCompression_mem (ρ x) (Q x) hx

end KadisonSimilarity

end

end OAI
