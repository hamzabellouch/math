import OAI.Analysis.KadisonKastler.RegularCoreConjugateGenerators
import OAI.Analysis.KadisonKastler.RegularLocalizationReconstruction

namespace OAI

/-! # The commutant identity for the regular modular conjugation -/

namespace KadisonKastler

open MeasureTheory Generator

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x))
  (M : VonNeumannAlgebra H)
  (hJM : conjugateRightAlgebra J hJ M = M.commutant)

include hJM in
private theorem right_constant_mem (a : H →L[ℂ] H) (ha : a ∈ M) :
    conjugationOperator J a ∈ M.commutant := by
  rw [← hJM]
  exact ⟨a, ha, rfl⟩

include hJM in
private theorem exists_left_of_right (z : H →L[ℂ] H) (hz : z ∈ M.commutant) :
    ∃ a ∈ M, conjugationOperator J a = z := by
  rw [← hJM] at hz
  exact hz

include hJU hJM in
theorem regularCoreConjugation_image :
    conjugateRightAlgebra (regularCoreConjugation U hU J)
      (regularCoreConjugation_involutive U hU J hJ hJU) (regularCoreAlgebra U hU M) =
      regularCommutantAlgebra U M := by
  let C := regularCoreConjugation U hU J
  have hC := regularCoreConjugation_involutive U hU J hJ hJU
  let R := regularCommutantAlgebra U M
  have hpre : regularCoreAlgebra U hU M ≤ conjugateRightAlgebra C hC R := by
    apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro a (⟨x, hx, rfl⟩ | ⟨s, rfl⟩)
    · change regularCoreEmbedding U hU x ∈ conjugateRightAlgebra C hC R
      refine ⟨conjugationOperator C (regularCoreEmbedding U hU x), ?_,
        conjugationOperator_twice C hC _⟩
      rw [regularCoreConjugation_embedding U hU J hJU]
      exact subset_generatedVonNeumannAlgebra _ (StarAlgebra.subset_adjoin ℂ _
        (Or.inl ⟨conjugationOperator J x, right_constant_mem J hJ M hJM x hx, rfl⟩))
    · change (regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈ conjugateRightAlgebra C hC R
      refine ⟨conjugationOperator C (regularRightTranslation (H := H) s), ?_,
        conjugationOperator_twice C hC _⟩
      change conjugationOperator (regularCoreConjugation U hU J)
        (regularRightTranslation (H := H) (Multiplicative.ofAdd s.toAdd)) ∈ R
      rw [regularCoreConjugation_translation U hU J hJU hJ]
      exact subset_generatedVonNeumannAlgebra _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨Multiplicative.ofAdd (-s.toAdd), rfl⟩))
  apply le_antisymm
  · intro T hT
    rcases hT with ⟨a, ha, rfl⟩
    rcases hpre ha with ⟨b, hb, he⟩
    have hback := congrArg (conjugationOperator C) he
    rw [conjugationOperator_twice C hC] at hback
    exact hback ▸ hb
  · apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro a (⟨z, hz, rfl⟩ | ⟨s, rfl⟩)
    · obtain ⟨x, hx, rfl⟩ := exists_left_of_right J hJ M hJM z hz
      change regularConstantHom volume (conjugationOperator J x) ∈
        conjugateRightAlgebra C hC (regularCoreAlgebra U hU M)
      exact ⟨regularCoreEmbedding U hU x, regularCoreEmbedding_mem_core U hU M hx,
        regularCoreConjugation_embedding U hU J hJU x⟩
    · change (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈
        conjugateRightAlgebra C hC (regularCoreAlgebra U hU M)
      refine ⟨(regularRightTranslation (H := H) (Multiplicative.ofAdd (-s.toAdd)) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H),
        regularTranslation_mem_core U hU M _, ?_⟩
      simpa only [neg_neg, ofAdd_toAdd] using
        regularCoreConjugation_translation U hU J hJU hJ (-s.toAdd)

include hJU hJM in
theorem regularCoreConjugation_commutant [TopologicalSpace.SeparableSpace H]
    (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M) :
    conjugateRightAlgebra (regularCoreConjugation U hU J)
      (regularCoreConjugation_involutive U hU J hJ hJU) (regularCoreAlgebra U hU M) =
      (regularCoreAlgebra U hU M).commutant := by
  rw [regularCoreConjugation_image U hU J hJ hJU M hJM]
  exact (publishedRegularCommutant H U hU M hn).symm

end

end KadisonKastler

end OAI
