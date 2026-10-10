import OAI.Analysis.FactorGeneration.Expectations
import OAI.Analysis.KadisonSimilarity.Tracial.TracialExpectations
import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteHalfProjection

namespace OAI

/-! The exact trace-pairing expectation consumed by the free-corner proof is
constructed on concrete finite tracial von Neumann inclusions and transported
through faithful algebra coordinates. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

section Concrete
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {N M : VonNeumannAlgebra H}

local instance expectationAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

def concreteTracialExpectation (τ : TracialRepresentation M) (hNM : N ≤ M) :
    TracialExpectation (concreteTraceLinear τ) (insideAlgebra (M := M) (P := N)) where
  map := (conditionalExpectationCLM τ hNM).toLinearMap
  range x := conditionalExpectation_mem τ hNM x
  pairing x c hc := by
    have h := conditionalExpectation_orthogonal τ hNM x ⟨c, hc⟩
    change τ.trace (c * (x - conditionalExpectation τ hNM x)) = 0 at h
    rw [mul_sub, trace_sub] at h
    exact (sub_eq_zero.mp h).symm

theorem concreteTracialExpectation_norm_le (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖(concreteTracialExpectation τ hNM).map x‖ ≤ ‖x‖ :=
  conditionalExpectation_norm_le τ hNM x

end Concrete

section Transport
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Transport the trace-pairing characterization to the inverse image of
the same concrete subalgebra. Only the actual trace identity is required. -/
def TracialExpectation.comapEquiv
    {τA : A →ₗ[ℂ] ℂ} {τB : B →ₗ[ℂ] ℂ} {S : StarSubalgebra ℂ B}
    (E : TracialExpectation τB S) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB (e a) = τA a) :
    TracialExpectation τA (S.comap e.toStarAlgHom) where
  map := e.symm.toAlgEquiv.toLinearMap.comp (E.map.comp e.toAlgEquiv.toLinearMap)
  range x := by
    change e (e.symm (E.map (e x))) ∈ S
    rw [e.apply_symm_apply]
    exact E.range (e x)
  pairing x c hc := by
    change τA (c * e.symm (E.map (e x))) = τA (c * x)
    rw [← hτ, map_mul, e.apply_symm_apply, E.pairing (e x) (e c) hc,
      ← map_mul, hτ]

end Transport
end KadisonSimilarity

end

end OAI
