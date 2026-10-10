import OAI.Analysis.KadisonKastler.PublishedModularSpectral
import OAI.Analysis.KadisonKastler.RegularCoreAlgebra

namespace OAI

/-! # Independence of the faithful-state modular core

Blackadar, *Operator Algebras*, III.4.8.1 (p.329), identifies the cores
of faithful normal semifinite weights. The cocycle is furnished by the
Connes Radon--Nikodym theorem III.4.7.5 (p.327). The same statement
applies after a normal star isomorphism, so it is independent of the
faithful representation. Only an algebraic core isomorphism is retained.
-/

namespace KadisonKastler

noncomputable section

universe u

def PublishedModularCoreIsomorphism : Prop :=
  ∀ (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K),
    (Algebra M ≃⋆ₐ[ℂ] Algebra N) →
    ∀ (Ω : H) (ξ : K), ‖Ω‖ = 1 → ‖ξ‖ = 1 →
      DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
      DenseRange (algebraVectorMap N ξ) → Function.Injective (algebraVectorMap N ξ) →
      ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
        (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x)),
      (∀ t x, x ∈ M → unitaryConj (U t) x ∈ M) → IsModularStateGroup M Ω U →
      ∀ (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
        (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x)),
      (∀ t x, x ∈ N → unitaryConj (V t) x ∈ N) → IsModularStateGroup N ξ V →
      Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
        Algebra (regularCoreAlgebra V hV N))

end

end KadisonKastler

end OAI
