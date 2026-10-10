import OAI.Combinatorics.TriangleFace.Model

namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem restriction_extension (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (x : E → ℝ) :
    oldRestriction (localExtension G c v hc x) = x := rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem localExtension_injective (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) : Function.Injective (localExtension G c v hc) := by
  intro x y h
  exact congrArg (oldRestriction : (E ⊕ Fin 3 → ℝ) →ₗ[ℝ] (E → ℝ)) h

end TriangleFace198
end

end OAI
