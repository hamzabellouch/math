import OAI.Analysis.KadisonSimilarity.Representation.CommonCentralData
import OAI.Analysis.KadisonSimilarity.Representation.CommonFiberRepresentations
import OAI.Analysis.KadisonSimilarity.Representation.CommonFiberFactors
import OAI.Analysis.KadisonSimilarity.Tracial.CentralCStarSource
import OAI.Analysis.KadisonSimilarity.Representation.CentralFactorAssembly

namespace OAI

/-! The separable central model is constructed from the represented
algebra. All norm, density and factor-fiber properties are proved. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped IsMulCommutative

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Construct the central factor decomposition needed by the manuscript's
separable estimate, including possible zero fibers. -/
theorem exists_publishedSeparableModel (P : VonNeumannAlgebra H) :
    Nonempty (PublishedSeparableModel P) := by
  obtain ⟨A, hAclosed, hAsep, hAcomm, _hA, hcentral⟩ := exists_separable_central_source P
  let : IsClosed (A : Set (H →L[ℂ] H)) := hAclosed
  let : TopologicalSpace.SeparableSpace A := hAsep
  let : IsMulCommutative A := hAcomm
  let π := A.subtype
  let D := cyclicDecompositionData π.range
  let : MeasurableSpace (WeakDual.characterSpace ℂ A) := commonCyclicMeasurable
  let : BorelSpace (WeakDual.characterSpace ℂ A) := commonCyclicBorel
  let := commonCyclicCountable π D
  have hcentral' : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant := by
    simpa only [π, subtype_star_range] using hcentral
  obtain ⟨B, C, hBclosed, hCclosed, hBsep, hCsep, hB, hC, hBgen, _hCgen, hSgen⟩ :=
    exists_separable_joint_cstar_source P
  let : IsClosed (B : Set (H →L[ℂ] H)) := hBclosed
  let : IsClosed (C : Set (H →L[ℂ] H)) := hCclosed
  let : TopologicalSpace.SeparableSpace B := hBsep
  let : TopologicalSpace.SeparableSpace C := hCsep
  have hSgen' : representationVonNeumannAlgebra (jointCStarSource B C).subtype =
      starSubalgebraCommutant π.range := by
    rw [representationVonNeumannAlgebra, subtype_star_range, hSgen, hcentral']
  have hcomm (b : jointCStarSource B C) (a : A) :
      (b : H →L[ℂ] H) * π a = π a * b := by
    have hb : (b : H →L[ℂ] H) ∈ starSubalgebraCommutant π.range := by
      rw [← hSgen']
      exact mem_representationVonNeumannAlgebra (jointCStarSource B C).subtype b
    exact commutant_commutes_representation π ⟨b.val, hb⟩ a
  obtain ⟨s, hs, hnull, ρ, hρ⟩ := exists_conull_common_representations π D
    (jointCStarSource B C).subtype hcomm
  let φ := StarSubalgebra.inclusion (le_jointCStarSource_left B C)
  let ρB := fun x => unitizationRestrict φ (ρ x)
  have hρB (b : B) (f : CommonCyclicHilbert π D) :
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρB x (Unitization.inr b) (f x) := by
    have h := hρ (φ b) f
    change ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
      (cyclicCommonBaseMeasure π D),
      isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
        ρ x (Unitization.inr (φ b)) (f x) at h
    simpa only [ρB, unitizationRestrict_inr] using h
  have hBgen' : representationVonNeumannAlgebra B.subtype = P := by
    rw [representationVonNeumannAlgebra, subtype_star_range]
    exact hBgen
  let DC := commonProjectionCentralData π D P B hB hBgen' hcentral' s hs hnull ρB hρB
  have hBC (b : B) (c : C) :
      (b : H →L[ℂ] H) * (c : H →L[ℂ] H) =
        (c : H →L[ℂ] H) * (b : H →L[ℂ] H) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp (hC c.property)) b (hB b.property)
  have hfactor := ae_common_fiber_scalar_center π D B C hBC hSgen' s hs hnull ρ hρ
  exact ⟨publishedSeparableModel_of_central_factors P (cyclicCommonBaseMeasure π D)
    (conullProjectionFiber s ρB) DC hfactor⟩

/-- Every separable represented von Neumann algebra admits the central
factor decomposition used in the uniform commutator estimate. -/
theorem publishedUniformInputs : PublishedUniformInputs.{u} :=
  ⟨fun _ _ _ _ _ P => exists_publishedSeparableModel P⟩

end KadisonSimilarity

end

end OAI
