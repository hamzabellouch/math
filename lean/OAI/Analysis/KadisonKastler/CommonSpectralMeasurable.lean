import OAI.Analysis.KadisonSimilarity.Representation.CommonFiberRepresentations
import OAI.Analysis.KadisonSimilarity.Representation.CommonCentralData
import OAI.Analysis.KadisonSimilarity.Representation.CommonFiberFactors
import OAI.Analysis.KadisonSimilarity.Tracial.CentralCStarSource
import OAI.Analysis.KadisonKastler.MeasurableConullRepresentations

namespace OAI

/-! # Borel representations in the common spectral model

The common spectral construction gives representations and their L²
action. A common-conull modification supplies Borel vector evaluations
for every source element while retaining that action.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance commonCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance commonCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

theorem exists_measurable_common_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ ρ : WeakDual.characterSpace ℂ A → B →⋆ₙₐ[ℂ]
        (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
      (∀ b v, Measurable fun x => ρ x b v) ∧
      ∀ (b : B) (f : CommonCyclicHilbert π D),
        ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
          isometricExtension (cyclicCommonEmbedding π D) (σ b) f x = ρ x b (f x) := by
  obtain ⟨ρ, hρ⟩ := exists_common_nonunital_representations π D σ hσ
  have hm (b : B) (v : ScalarHilbertCoordinates D.generators) :
      AEStronglyMeasurable (fun x => ρ x b v) (cyclicCommonBaseMeasure π D) := by
    let f : CommonCyclicHilbert π D := Lp.const 2 (cyclicCommonBaseMeasure π D) v
    have he : ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
        isometricExtension (cyclicCommonEmbedding π D) (σ b) f x = ρ x b v := by
      filter_upwards [hρ b f, Lp.coeFn_const (cyclicCommonBaseMeasure π D) v (p := 2)]
        with x hx hf
      simpa only [f, hf, Function.const_apply] using hx
    exact (Lp.aestronglyMeasurable _).congr he
  obtain ⟨τ, hτm, hτ⟩ := exists_measurable_nonunitalRepresentation_version
    (cyclicCommonBaseMeasure π D) ρ hm
  refine ⟨τ, hτm, ?_⟩
  intro b f
  filter_upwards [hρ b f, hτ b] with x hx he
  rw [he]
  exact hx

end

end KadisonKastler

end OAI
