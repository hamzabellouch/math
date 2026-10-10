import OAI.Analysis.FactorGeneration.ProjectionComparison
import OAI.Analysis.FactorGeneration.FiniteComparison
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # Equal-trace projection conjugacy in a concrete finite factor -/

namespace KadisonKastler

open Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Faithfulness of a represented trace makes every isometry unitary. -/
theorem tracial_isometry_coisometry (τ : TracialRepresentation M)
    (a : Algebra M) (ha : star a * a = 1) : a * star a = 1 := by
  let v : PartialIsometry M := ⟨⟨1, IsStarProjection.one _⟩, a, ha⟩
  have hle : v.target ≤ (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) := by
    change 1 * v.target.val = v.target.val
    exact one_mul _
  have he : v.target = (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) := by
    apply projection_eq_of_le_of_trace_eq τ hle
    change τ.trace (a * star a) = τ.trace 1
    rw [τ.trace_mul_comm, ha]
  exact congrArg Subtype.val he

/-- Equal trace projections are conjugate by an actual unitary of the factor. -/
theorem exists_tracial_projection_conjugacy (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (p q : AlgebraProjection M) (ht : τ.trace p.val = τ.trace q.val) :
    ∃ u : unitary (Algebra M), (u : Algebra M) * p.val * star (u : Algebra M) = q.val := by
  obtain ⟨a, ha, hq⟩ := exists_partialIsometry_of_trace_eq τ hfactor p q ht
  let v : PartialIsometry M := ⟨p, a, ha⟩
  obtain ⟨u, hu⟩ := v.exists_unitary_extension hfactor (tracial_isometry_coisometry τ)
  have hproj : (u : Algebra M) * p.val * star (u : Algebra M) =
      ((u : Algebra M) * p.val) * star ((u : Algebra M) * p.val) := by
    rw [star_mul, p.property.isSelfAdjoint.star_eq]
    calc
      (u : Algebra M) * p.val * star (u : Algebra M) =
          (u : Algebra M) * (p.val * p.val) * star (u : Algebra M) := by
        rw [p.property.isIdempotentElem.eq]
      _ = _ := by simp only [mul_assoc]
  refine ⟨u, ?_⟩
  rw [hproj, hu]
  exact hq

end

end KadisonKastler

end OAI
