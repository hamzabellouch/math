import OAI.Analysis.IrrationalRotation.Model.AffiliatedTransport
import OAI.Analysis.IrrationalRotation.Model.VectorTraceState

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Invariant233

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def IsNormalFaithfulTracialState (M : VonNeumannAlgebra E) (τ : TracialState M) : Prop :=
  (∀ a : M, (a : E →L[ℂ] E).IsPositive → τ a = 0 → a = 0) ∧
  (∀ (ι : Type u) (L : Filter ι), L.NeBot → ∀ (a : ι → M) (b : M),
    (∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) →
    (∀ x : E, Tendsto (fun i => (a i : E →L[ℂ] E) x) L
      (𝓝 ((b : E →L[ℂ] E) x))) →
    Tendsto (fun i => τ (a i)) L (𝓝 (τ b)))

def IsAffiliated (M : VonNeumannAlgebra E) (H : E →ₗ.[ℂ] E) : Prop :=
  ∀ U : unitary (E →L[ℂ] E), (U : E →L[ℂ] E) ∈ M.commutant →
    ∃ hD : ∀ x : H.domain, (U : E →L[ℂ] E) (x : E) ∈ H.domain,
      ∀ x : H.domain,
        H ⟨(U : E →L[ℂ] E) (x : E), hD x⟩ = (U : E →L[ℂ] E) (H x)

def IsPositivePartial (H : E →ₗ.[ℂ] E) : Prop :=
  ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re

end Invariant233

end

end OAI
