import OAI.Analysis.FactorGeneration.Generation
import OAI.Analysis.RelativeGeneration.LocusTopology

namespace OAI

noncomputable section

open scoped Topology

/- The whole relative-generating locus, not only a residual subset. -/
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

/-- Full represented theorem: the previously proved residual subset is reused only for density. -/
theorem represented_full_relative_generation
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ r : N.toStarSubalgebra, IsStarProjection r → r ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    IsGδ {u : TraceUnitary τ |
      wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}) = M.toStarSubalgebra} ∧
    Dense {u : TraceUnitary τ |
      wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}) = M.toStarSubalgebra} := by
  have he : {u : TraceUnitary τ |
      wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}) = M.toStarSubalgebra} =
      {u : TraceUnitary τ | relativeGenerated (N := N) τ u = M} := by
    ext u
    change (relativeGenerated (N := N) τ u).toStarSubalgebra = M.toStarSubalgebra ↔ _
    constructor
    · intro h
      apply VonNeumannAlgebra.ext
      intro x
      change x ∈ (relativeGenerated (N := N) τ u).toStarSubalgebra ↔ x ∈ M.toStarSubalgebra
      rw [h]
    · exact fun h => congrArg _ h
  refine ⟨he.symm ▸ relativeGeneratingLocus_isGδ τ hNM hsep, ?_⟩
  obtain ⟨C,_,hC,hm⟩ := represented_relative_generation τ hNM hfactor hdiff hirr hsep
  exact hC.mono hm

end Generator.Tracial

end

end OAI
