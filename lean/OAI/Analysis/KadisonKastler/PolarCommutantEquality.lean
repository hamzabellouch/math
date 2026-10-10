import OAI.Analysis.KadisonKastler.PolarCommutantDuality

namespace OAI

/-! # The polar commutant equality from the averaged inclusion -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaPolarConjugation_commutant_eq_of_inclusion
    (hincl : ∀ b : Algebra M.commutant,
      conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val ∈ M) :
    conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant := by
  have hreverse := polar_commutant_reverse (tomitaPolarConjugation J Ω hsep hcyc)
    (tomitaPolarConjugation_involutive J Ω hsep hcyc) Ω
    (tomitaPolarConjugation_fixes_vector J Ω hsep hcyc) hcyc hsep
    (tomitaPolarConjugation_vectorState J Ω hsep hcyc) hincl
  apply le_antisymm
  · rintro T ⟨a, ha, rfl⟩
    exact hreverse ⟨a, ha⟩
  · intro T hT
    exact ⟨conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) T,
      hincl ⟨T, hT⟩,
      conjugationOperator_twice _ (tomitaPolarConjugation_involutive J Ω hsep hcyc) T⟩

end

end KadisonKastler

end OAI
