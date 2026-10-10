import OAI.Analysis.KadisonKastler.TrivialCoreCenter
import OAI.Analysis.KadisonKastler.TracialModularResolution
import OAI.Analysis.KadisonKastler.KMSUniqueness
import OAI.Analysis.KadisonKastler.HilbertConjugation

namespace OAI

/-! # Tracial vector states have nonfactorial modular cores -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem regularCore_not_factor_of_tracial_vector
    (Ω : H) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (htrace : ∀ a b : Algebra M,
      inner ℂ Ω ((a.val * b.val) Ω) = inner ℂ Ω ((b.val * a.val) Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := H)
  have he := kmsGroup_eq_constructed J Ω hsep hcyc U hU hn hm
  apply regularCore_not_factor_of_trivial U hU
  intro t
  rw [he]
  exact modularStrongGroup_tracial J Ω hsep hcyc htrace t

end

end KadisonKastler

end OAI
