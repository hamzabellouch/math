import Mathlib
import OAI.Analysis.FreeWords.VariableUltraBundle

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKUltraTrace

open Filter Topology

open scoped ComplexOrder BoundedContinuousFunction

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]

local instance projUltraOrder : PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance : LE (coordinateAlgebra R) := (projUltraOrder R).toLE

local instance : Preorder (coordinateAlgebra R) := (projUltraOrder R).toPreorder

local instance : StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

theorem coordinate_projection (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ)
    (p : ℕ → A) (hp : ∀ j, IsStarProjection (p j)) (hpR : ∀ j, p j∈R j)
    (c : ℂ) (hc : Tendsto (fun j => τ (p j)) (ω : Filter ℕ) (𝓝 c)) :
    ∃ q : ConcreteAlgebra (gnsVonNeumann (coordinateTrace R τ ω)),
      IsStarProjection q ∧
      (gnsNormalTrace _ (coordinateTrace_one R τ ω h1) (coordinateTrace_tracial R τ ω htr)).map q=c := by
  let p₀ : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroup p
    continuous_of_discreteTopology 1 (fun j => (hp j).norm_le)
  let a : coordinateAlgebra R := ⟨p₀,hpR⟩
  have ha : IsStarProjection a := by
    constructor
    · apply Subtype.ext
      ext j
      exact (hp j).isIdempotentElem.eq
    · apply Subtype.ext
      ext j
      exact (hp j).isSelfAdjoint.star_eq
  refine ⟨gnsBiHom (coordinateTrace R τ ω) a,ha.map _,?_⟩
  rw [gnsNormalTrace_image]
  exact tendsto_nhds_unique (tendsto_ultraTraceValue τ ω p₀) hc

end

end KKVariableUltra
end

end OAI
