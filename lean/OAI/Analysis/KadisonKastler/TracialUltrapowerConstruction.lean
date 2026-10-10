import OAI.Analysis.KadisonKastler.TracialConstantEmbedding
import OAI.Analysis.KadisonKastler.TracialVarianceControl
import OAI.Analysis.KadisonKastler.PublishedUltrapower
import OAI.Analysis.KadisonKastler.TracialSequenceFactor

namespace OAI

/-! # The constant II₁ tracial ultrapower

This constructs the bounded-product quotient, its faithful trace and its
finite factor representation, as in Popa, JFA 266 (2014), §1.6.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def constructedTracialUltrapower (M : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) :
    TracialUltrapower (concreteFactorTrace hM) ω := by
  letI : Nontrivial (Algebra M) := ⟨⟨0, 1, fun h => hM.nonzero (congrArg Subtype.val h)⟩⟩
  let τ : ∀ _ : ℕ, FaithfulTracialState (Algebra M) := fun _ => concreteFactorTrace hM
  let d := constructedTracialSequenceFactor τ ω hω
    (fun _ x => exists_unitary_trace_variance_control hM x)
    (tracialConstantQuotient_infinite (concreteFactorTrace hM) ω
      (not_finiteDimensional_of_isII1Factor M hM))
  exact {
    H := d.H
    algebra := d.algebra
    factor := d.factor
    quotient := d.quotient.comp boundedToVarying
    surjective := d.surjective.comp boundedToVarying_surjective
    trace_limit := fun x => d.trace_limit (boundedToVarying (A := Algebra M) x) }

/-- The constant-sequence tracial ultrapower of Popa §1.6. -/
theorem publishedTracialUltrapower : PublishedTracialUltrapower.{u} := by
  intro H _ _ _ M hM ω hω
  exact ⟨constructedTracialUltrapower M hM ω hω⟩

end

end KadisonKastler

end OAI
