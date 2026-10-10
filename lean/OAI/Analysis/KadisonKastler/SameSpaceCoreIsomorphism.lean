import OAI.Analysis.KadisonKastler.KMSUniqueness
import OAI.Analysis.KadisonKastler.ConstructedCoreStateIndependence

namespace OAI

/-! # Core independence for arbitrary KMS implementations on the same space -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem modularCore_equiv_of_two_states (M : VonNeumannAlgebra H) (Ω ξ : H)
    (hΩc : DenseRange (algebraVectorMap M Ω)) (hξc : DenseRange (algebraVectorMap M ξ))
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hξs : Function.Injective (algebraVectorMap M ξ))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M) (hKU : IsModularStateGroup M Ω U)
    (V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M) (hKV : IsModularStateGroup M ξ V) :
    Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra V hV M)) := by
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := H)
  have heU := kmsGroup_eq_constructed J Ω hΩs hΩc U hU hnU hKU
  have heV := kmsGroup_eq_constructed J ξ hξs hξc V hV hnV hKV
  subst U
  subst V
  exact constructedCore_equiv_of_two_states M Ω ξ hΩc hξc hΩs hξs J J

end

end KadisonKastler

end OAI
