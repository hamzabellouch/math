import OAI.Analysis.KadisonKastler.ConstructedCoreFiniteWindow
import OAI.Analysis.KadisonKastler.KMSUniqueness

namespace OAI

/-! # Finite frequency windows for every KMS implementation

Uniqueness of the modular implementation transfers the constructed
finite projection to any strongly continuous normalizing KMS group
of the given cyclic separating vector.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
  (hm : IsModularStateGroup M Ω U)

include J Ω hsep hcyc hn hm in
theorem modularCore_unitWindow_finite :
    FiniteProjectionIn (regularCoreAlgebra U hU M)
      (unitCoreFrequencyProjection U hU M).val := by
  have he := kmsGroup_eq_constructed J Ω hsep hcyc U hU hn hm
  subst U
  exact constructedCore_unitWindow_finite J Ω hsep hcyc

include J Ω hsep hcyc hn hm in
theorem modularFactorialCore_projectionSemifinite [Nontrivial H]
    (hfactor : ScalarCenter (regularCoreAlgebra U hU M)) :
    ∀ p : AlgebraProjection (regularCoreAlgebra U hU M), p.val ≠ 0 →
      ∃ q : AlgebraProjection (regularCoreAlgebra U hU M),
        q ≤ p ∧ q.val ≠ 0 ∧ FiniteProjectionIn (regularCoreAlgebra U hU M) q.val := by
  exact projectionSemifinite_of_finite_projection hfactor
    (unitCoreFrequencyProjection U hU M) (unitCoreFrequencyProjection_ne_zero U hU M)
    (modularCore_unitWindow_finite J Ω hsep hcyc U hU hn hm)

end

end KadisonKastler

end OAI
