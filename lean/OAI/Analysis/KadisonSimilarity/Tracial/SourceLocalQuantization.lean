import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorPresentation
import OAI.Analysis.KadisonSimilarity.Tracial.RelativeMatrixQuantization
import OAI.Analysis.KadisonSimilarity.Tracial.InternalSourceStages

namespace OAI

/-! Relative local quantization for the actual source in the constructed
finite-factor presentation. Every small projection lies in that source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : VonNeumannAlgebra H}

namespace FiniteFactorPresentation
variable (F : FiniteFactorPresentation P)

local instance sourceQuantizationAmbientNontrivial : Nontrivial F.N.toStarSubalgebra := by
  refine nontrivial_of_ne (0 : F.N.toStarSubalgebra) 1 ?_
  intro h
  have ht := congrArg F.representation.trace h
  rw [F.representation.trace_one] at ht
  change inner ℂ F.representation.vector
    ((0 : F.K →L[ℂ] F.K) F.representation.vector) = 1 at ht
  simp at ht

local instance sourceQuantizationSourceNontrivial : Nontrivial (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra := by
  refine nontrivial_of_ne (0 : (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra) 1 ?_
  intro h
  exact F.source.source_factor.nonzero (congrArg Subtype.val h)

/-- Centered ambient coefficients admit a nonzero, arbitrarily small source
projection on which all compressions have arbitrarily small trace norm. -/
theorem exists_small_source_compression {I : Type*} [Fintype I]
    (x : I → F.N.toStarSubalgebra) (hx : ∀ i, F.representation.trace (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra,
      IsStarProjection q ∧ q ≠ 0 ∧
      (F.representation.trace
        (coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le F.source.stages) q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional F.N F.representation.vector).toPreGNS
        (coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le F.source.stages) q * x i *
          coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le F.source.stages) q)‖ ^ 2 <
        δ * (F.representation.trace
          (coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le F.source.stages) q)).re := by
  apply exists_source_small_projection F.representation
    (FiniteMatrixStage.generatedVonNeumann_le F.source.stages)
    F.source.source_factor.factor F.source.source_factor.diffuse
    (fun c hc => F.source.irreducible c (fun a => ?_))
    (generatedInternalStage F.source.stages)
    (generatedInternalStage_sizes_cofinal F.source.stages F.source.monotone
      F.source.source_factor.diffuse) x hx hδ hη
  have h := hc a
  exact congrArg Subtype.val h

end FiniteFactorPresentation
end KadisonSimilarity

end

end OAI
