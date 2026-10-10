import OAI.Analysis.KadisonKastler.PinchedVectorState
import OAI.Analysis.KadisonKastler.NormalCyclicCore

namespace OAI

/-! # A faithful state with a tracial corner has a nonfactorial modular core -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem regularCore_not_factor_of_tracial_corner
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (htrace : ∀ a b : Algebra M,
      inner ℂ Ω ((p.val * a * p.val * b * p.val).val Ω) =
        inner ℂ Ω ((p.val * b * p.val * a * p.val).val Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  exact regularCore_not_factor_of_centralizing_vector_representation
    (pinchedRepresentation M) (pinchedVector p Ω) (pinchedVector_separating p Ω hsep)
    pinchedRepresentation_normal Ω hsep hcyc p hp0
    (pinchedVector_centralizes_corner p Ω htrace) U hU hn hm

end

end KadisonKastler

end OAI
