import OAI.Analysis.KadisonKastler.ConstructedCoreTypeIIInfinity
import OAI.Analysis.KadisonKastler.SameSpaceCoreIsomorphism
import OAI.Analysis.KadisonKastler.HilbertConjugation
import OAI.Analysis.KadisonKastler.PublishedModularCoreType

namespace OAI

/-! # Type II infinity for factorial KMS cores

The core classification is constructed independently of whether the source
algebra has type III. The latter condition remains explicit in the final
type III-one adapter.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem modularFactorialCore_typeIIInfinity
    (Ω : H) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) (hf : ScalarCenter (regularCoreAlgebra U hU M)) :
    TypeIIInfinityFactor (regularCoreAlgebra U hU M) := by
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := H)
  have he := kmsGroup_eq_constructed J Ω hsep hcyc U hU hn hm
  subst U
  exact constructedFactorialCore_typeIIInfinity J Ω hsep hcyc hf

/-- Once the source's ordinary type III condition is known, the entire
remaining type III-one core clause follows from one factorial core. -/
theorem typeIII1_of_typeIII_of_factorialCore
    (hM : TypeIIIFactor M) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) (hf : ScalarCenter (regularCoreAlgebra U hU M)) :
    TypeIII1Factor M := by
  refine ⟨hM, ?_⟩
  intro ξ _ hξc hξs V hV hnV hmV
  obtain ⟨e⟩ := modularCore_equiv_of_two_states M Ω ξ hcyc hξc hsep hξs
    U hU hn hm V hV hnV hmV
  exact (modularFactorialCore_typeIIInfinity Ω hsep hcyc U hU hn hm hf).of_starAlgEquiv e

end

end KadisonKastler

end OAI
