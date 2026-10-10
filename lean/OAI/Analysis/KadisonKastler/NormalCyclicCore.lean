import OAI.Analysis.KadisonKastler.NormalCyclicRealization
import OAI.Analysis.KadisonKastler.NormalCentralizingCorner

namespace OAI

/-! # A normal vector realization with a centralizing corner obstructs a factor core -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H}

theorem regularCore_not_factor_of_centralizing_vector_representation
    (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (η : K)
    (hs : Function.Injective (fun a : Algebra M => φ a η)) (hφ : BoundedWeakNormal M φ)
    (Ω : H) (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hΩc : DenseRange (algebraVectorMap M Ω))
    (p : AlgebraProjection M) (hp : p.val ≠ 0)
    (hc : ∀ a b : Algebra M, inner ℂ η (φ (p.val * a * p.val * b) η) =
      inner ℂ η (φ (b * (p.val * a * p.val)) η))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  exact regularCore_not_factor_of_normal_centralizing_corner
    (normalCyclicEquiv M φ η hs hφ) (normalCyclicEquiv_normal M φ η hs hφ)
    Ω (normalCyclicVector M φ η) hΩs hΩc
    (normalCyclicAlgebra_separating M φ η hs hφ) (normalCyclicAlgebra_cyclic M φ η)
    p hp (fun a => normalCyclicEquiv_centralizes M φ η hs hφ _ (hc a)) U hU hn hm

end

end KadisonKastler

end OAI
