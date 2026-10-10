import OAI.Analysis.KadisonKastler.RegularCoreStandardConjugation
import OAI.Analysis.KadisonKastler.ModularSpectralConstruction

namespace OAI

/-! # The constructed modular core has an explicit commutant conjugation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularStrongGroup_polar_commutes (t : Multiplicative ℝ) (x : H) :
    tomitaPolarConjugation J Ω hsep hcyc
      ((modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) x) =
    (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H)
      (tomitaPolarConjugation J Ω hsep hcyc x) := by
  have h := congrArg (fun A : H →L[ℂ] H => A (tomitaPolarConjugation J Ω hsep hcyc x))
    (modularStrongGroup_polar_conjugation J Ω hsep hcyc t.toAdd)
  simpa only [conjugationOperator_apply, ofAdd_toAdd,
    tomitaPolarConjugation_involutive J Ω hsep hcyc x] using h

theorem constructedCore_has_commutant_conjugation :
    ∃ C : RegularCoreHilbert H ≃ₗᵢ⋆[ℂ] RegularCoreHilbert H,
      ∃ hC : Function.Involutive C,
        conjugateRightAlgebra C hC
          (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
            (modularStrongGroup_continuous J Ω hsep hcyc) M) =
        (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) M).commutant := by
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  let P := tomitaPolarConjugation J Ω hsep hcyc
  have hP := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have hPU := modularStrongGroup_polar_commutes J Ω hsep hcyc
  refine ⟨regularCoreConjugation U hU P,
    regularCoreConjugation_involutive U hU P hP hPU, ?_⟩
  apply regularCoreConjugation_commutant U hU P hP hPU M
    (tomitaPolarConjugation_commutant_eq J Ω hsep hcyc)
  intro t a ha
  have he := modularStrongGroup_normalizes J Ω hsep hcyc t
  change unitaryConj (U t) a ∈ (M : Set (H →L[ℂ] H))
  rw [← he]
  exact Set.mem_image_of_mem _ ha

end

end KadisonKastler

end OAI
