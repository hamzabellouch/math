import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteTracialExpectation
import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyDischarge

namespace OAI

/-! Membership in a concrete finite von Neumann subalgebra is detected by
its closed space of trace vectors. This identifies the normal range of the
bounded tracially generated algebra. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H}

/-- The trace-vector image of a concrete subalgebra. -/
def subalgebraTraceVectors (τ : TracialRepresentation M) (N : VonNeumannAlgebra H) : Set H :=
  baseVector τ '' {a : M.toStarSubalgebra | (a : H →L[ℂ] H) ∈ N}

/-- Orthogonality of the conditional expectation detects membership from
the closed trace-vector space, without a uniform bound on approximants. -/
theorem mem_of_traceVector_mem_closure (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra)
    (hx : baseVector τ x ∈ closure (subalgebraTraceVectors τ N)) :
    (x : H →L[ℂ] H) ∈ N := by
  let E := conditionalExpectation τ hNM x
  let y := x - E
  have hE : (E : H →L[ℂ] H) ∈ N := conditionalExpectation_mem τ hNM x
  have ho : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) y :=
    conditionalExpectation_orthogonal τ hNM x
  have hz (z : M.toStarSubalgebra) (hz : (z : H →L[ℂ] H) ∈ N) :
      inner ℂ (baseVector τ y) (baseVector τ z) = 0 := by
    apply inner_eq_zero_symm.mp
    rw [baseVector_inner_trace]
    exact ho ⟨star z, by change star (z : H →L[ℂ] H) ∈ N; exact star_mem hz⟩
  have hclosed : IsClosed {v : H | inner ℂ (baseVector τ y) v = 0} :=
    isClosed_eq (innerSL ℂ (baseVector τ y)).continuous continuous_const
  have hsub : subalgebraTraceVectors τ N ⊆ {v : H | inner ℂ (baseVector τ y) v = 0} := by
    rintro _ ⟨z, hzN, rfl⟩
    exact hz z hzN
  have hx0 : inner ℂ (baseVector τ y) (baseVector τ x) = 0 :=
    closure_minimal hsub hclosed hx
  have hyv : baseVector τ y = baseVector τ x - baseVector τ E := map_sub (baseVector τ) x E
  have hy0 : inner ℂ (baseVector τ y) (baseVector τ y) = 0 := by
    calc
      _ = inner ℂ (baseVector τ y) (baseVector τ x - baseVector τ E) :=
        congrArg (fun z => inner ℂ (baseVector τ y) z) hyv
      _ = 0 := by rw [inner_sub_right, hx0, hz E hE, sub_self]
  have hy : y = 0 := baseVector_injective τ (by
    rw [inner_self_eq_zero.mp hy0, map_zero])
  have hxe : x = E := sub_eq_zero.mp hy
  rwa [hxe]

theorem mem_iff_traceVector_mem_closure (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) :
    (x : H →L[ℂ] H) ∈ N ↔ baseVector τ x ∈ closure (subalgebraTraceVectors τ N) := by
  constructor
  · intro hx
    exact subset_closure ⟨x, hx, rfl⟩
  · exact mem_of_traceVector_mem_closure τ hNM x

end KadisonSimilarity

end

end OAI
