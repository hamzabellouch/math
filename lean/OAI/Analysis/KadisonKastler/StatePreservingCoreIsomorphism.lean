import OAI.Analysis.KadisonKastler.KMSUniqueness
import OAI.Analysis.KadisonKastler.StateCoreTransport

namespace OAI

/-! # Arbitrary KMS groups in state-preserving representations -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem modularCore_equiv_of_statePreserving
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
    (hM : DenseRange (algebraVectorMap M Ω)) (hN : DenseRange (algebraVectorMap N ξ))
    (hMsep : Function.Injective (algebraVectorMap M Ω))
    (hNsep : Function.Injective (algebraVectorMap N ξ))
    (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M) (hKU : IsModularStateGroup M Ω U)
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hnV : ∀ t a, a ∈ N → unitaryConj (V t) a ∈ N) (hKV : IsModularStateGroup N ξ V) :
    Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra V hV N)) := by
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := H)
  obtain ⟨L, _⟩ := exists_hilbert_conjugation (H := K)
  have heU := kmsGroup_eq_constructed J Ω hMsep hM U hU hnU hKU
  have heV := kmsGroup_eq_constructed L ξ hNsep hN V hV hnV hKV
  subst U
  subst V
  exact constructedCore_equiv_of_statePreserving θ Ω ξ hM hN hstate J L hMsep hNsep

end

end KadisonKastler

end OAI
