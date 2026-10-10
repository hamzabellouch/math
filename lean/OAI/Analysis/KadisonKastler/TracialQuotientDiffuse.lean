import OAI.Analysis.KadisonKastler.TracialQuotientFactor
import OAI.Analysis.KadisonKastler.FiniteType

namespace OAI

/-! # Infinite-dimensional tracial sequence factors are diffuse -/

namespace KadisonKastler

open Filter

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local instance : PartialOrder (TracialSequenceQuotient τ ω) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (TracialSequenceQuotient τ ω) := CStarAlgebra.spectralOrderedRing _

theorem tracialSequenceAlgebra_isII1 (hω : (ω : Filter ℕ) ≤ atTop)
    (hcontrol : CoordinateVarianceControl τ)
    (hinfinite : ¬ FiniteDimensional ℂ (TracialSequenceQuotient τ ω)) :
    Generator.IsII1Factor (tracialSequenceAlgebra τ ω).toStarSubalgebra := by
  let M := tracialSequenceAlgebra τ ω
  have hcenter : ScalarCenter M := by
    intro x hx hc
    obtain ⟨c, he⟩ := tracialSequenceAlgebra_scalarCenter τ ω hω hcontrol ⟨x, hx⟩
      (fun y => Subtype.ext (hc y.val y.property))
    exact ⟨c, congrArg Subtype.val he⟩
  have hnotType : ¬ IsTypeIFactor M := by
    intro ht
    let := ht.finiteDimensional (tracialSequenceAlgebra_finite τ ω hω)
    exact hinfinite (FiniteDimensional.of_injective
      (tracialSequenceEquiv τ ω hω).toAlgEquiv.toLinearMap (tracialSequenceEquiv τ ω hω).injective)
  refine {
    nonzero := ?_
    weaklyClosed := Generator.Tracial.vonNeumann_wotClosed M
    factor := tracialSequenceAlgebra_scalarCenter τ ω hω hcontrol
    finite := tracialSequenceAlgebra_finite τ ω hω
    diffuse := (isTypeIFactor_or_projectionDiffuse hcenter).resolve_left hnotType }
  intro h
  have he : traceStateRepresentation (tracialQuotientTrace τ ω) 0 =
      traceStateRepresentation (tracialQuotientTrace τ ω) 1 := by rw [map_zero, map_one, h]
  exact zero_ne_one (traceStateRepresentation_injective _ he)

end

end KadisonKastler

end OAI
