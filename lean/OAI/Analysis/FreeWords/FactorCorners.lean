import Mathlib
import OAI.Analysis.FreeWords.FactorStructure

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem trace_projection_ne_zero {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) {p : ConcreteAlgebra M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) : τ.map p ≠ 0 := by
  intro hτ
  apply hp0
  apply τ.faithful p _ hτ
  have he : star p*p=p := by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  have he' : star (p : H →L[ℂ] H)*(p : H →L[ℂ] H) = p := congrArg Subtype.val he
  rw [← he']
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem factor_nonzero_corner {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hM : KKFreeLiftFrontier.IsFactor M) {p q : ConcreteAlgebra M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    ∃ a : ConcreteAlgebra M, q*a*p ≠ 0 := by
  by_contra! hz
  let T : (tracePositive τ).GNS →L[ℂ] (tracePositive τ).GNS :=
    (tracePositive τ).gnsStarAlgHom q
  have ho : conjugacyOrbit τ p ⊆ {v | T v=0} := by
    rintro _ ⟨u,rfl⟩
    change (tracePositive τ).gnsStarAlgHom q (gnsVector (tracePositive τ)
      ((u : ConcreteAlgebra M)*p*star (u : ConcreteAlgebra M))) = 0
    rw [gnsStarAlgHom_vector]
    have he : q*((u : ConcreteAlgebra M)*p*star (u : ConcreteAlgebra M))=0 := by
      rw [← mul_assoc, ← mul_assoc, hz, zero_mul]
    rw [he, map_zero]
  have hh : conjugacyHull τ p ⊆ {v | T v=0} := by
    apply closure_minimal (convexHull_min ho ?_) (isClosed_eq T.continuous continuous_const)
    exact (T.restrictScalars ℝ).ker.convex
  have he := hh (factor_trace_in_conjugacyHull τ hM p)
  change (tracePositive τ).gnsStarAlgHom q (gnsVector (tracePositive τ) (τ.map p • 1))=0 at he
  rw [gnsStarAlgHom_vector, mul_smul_comm, mul_one] at he
  have hzero : τ.map p • q=0 := gnsVector_injective τ (he.trans (map_zero _).symm)
  exact hq0 ((smul_eq_zero.mp hzero).resolve_left (trace_projection_ne_zero τ hp hp0))

end

end KKProjectionSupport
end

end OAI
