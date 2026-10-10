import OAI.Analysis.FactorGeneration.ProjectionComparison
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem

namespace OAI

/-! The exact trace-comparison input used in the corner argument follows
from projection comparison in a concrete finite factor. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

local instance comparisonAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

theorem concrete_projection_trace_mono (τ : TracialRepresentation M)
    {p q : AlgebraProjection M} (hpq : p ≤ q) :
    (τ.trace p.val).re ≤ (τ.trace q.val).re := by
  have hd : IsStarProjection (q.val - p.val) :=
    p.property.sub_of_mul_eq_right q.property hpq
  have ht := projection_trace_sq τ (q.val - p.val) hd
  rw [trace_sub, Complex.sub_re] at ht
  nlinarith [sq_nonneg (τ.norm₂ (q.val - p.val))]

/-- In a finite factor, a projection of smaller trace embeds into the
larger projection. The partial isometry is constructed by the
maximality argument, and faithfulness removes the possible residual. -/
theorem finiteFactorProjectionComparison (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a * c = c * a) →
        ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra)) :
    FiniteFactorProjectionComparison (fun a : M.toStarSubalgebra => (τ.trace a).re) := by
  intro e r he hr htrace
  let p : AlgebraProjection M := ⟨r, hr⟩
  let q : AlgebraProjection M := ⟨e, he⟩
  obtain ⟨v, hvp, hvq, hfull⟩ := exists_partialIsometry_comparison τ hfactor p q
  have hsource : v.support = p := by
    rcases hfull with hs | ht
    · exact hs
    · apply projection_eq_of_le_of_trace_eq τ hvp
      rw [projection_trace_real τ v.support, projection_trace_real τ p]
      apply congrArg Complex.ofReal
      apply le_antisymm (concrete_projection_trace_mono τ hvp)
      rw [v.trace_support_eq_target τ, ht]
      exact htrace
  refine ⟨v.val, v.initial.trans (congrArg Subtype.val hsource), ?_⟩
  exact hvq

end KadisonSimilarity

end

end OAI
