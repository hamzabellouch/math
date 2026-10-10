import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.LinearAlgebra.Span.Basic

namespace OAI

/-! Equality of linear maps can be checked on unitaries. -/

namespace WeakPureInfiniteness

lemma linearMap_ext_unitaries {A X : Type*} [CStarAlgebra A]
    [AddCommMonoid X] [Module ℂ X] (f g : A →ₗ[ℂ] X)
    (h : ∀ u : unitary A, f u = g u) : f = g :=
  LinearMap.ext_on (CStarAlgebra.span_unitary A) (fun x hx => h ⟨x, hx⟩)

end WeakPureInfiniteness

end OAI
