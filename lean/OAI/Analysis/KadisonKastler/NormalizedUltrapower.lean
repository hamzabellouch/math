import OAI.Analysis.KadisonKastler.ConcreteTraceUniqueness
import OAI.Analysis.KadisonKastler.PublishedUltrapower

namespace OAI

/-! # Using the canonical ultrapower with an explicit normalized trace -/

namespace KadisonKastler

open Filter

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The published canonical construction also applies to an explicitly
constructed normalized faithful trace, since uniqueness identifies it
with the canonical trace on the same finite factor. -/
theorem publishedTracialUltrapower_for_trace
    (hpub : PublishedTracialUltrapower.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ : FaithfulTracialState (Algebra M))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) :
    Nonempty (TracialUltrapower τ ω) := by
  obtain ⟨Q⟩ := hpub H M hM ω hω
  refine ⟨{
    H := Q.H
    normedAddCommGroup := Q.normedAddCommGroup
    innerProductSpace := Q.innerProductSpace
    completeSpace := Q.completeSpace
    algebra := Q.algebra
    factor := Q.factor
    quotient := Q.quotient
    surjective := Q.surjective
    trace_limit := ?_ }⟩
  intro s
  have h := Q.trace_limit s
  have he : (fun j => τ.toLinearMap (s j)) =
      (fun j => (concreteFactorTrace hM).toLinearMap (s j)) := by
    funext j
    exact faithfulTracialState_eq_concreteFactorTrace hM τ (s j)
  rw [he]
  exact h

end

end KadisonKastler

end OAI
