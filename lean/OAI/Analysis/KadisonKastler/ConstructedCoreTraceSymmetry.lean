import OAI.Analysis.KadisonKastler.CoreTraceEmbeddingSymmetry
import OAI.Analysis.KadisonKastler.CoreTraceTranslationVector
import OAI.Analysis.KadisonKastler.CoreFrequencyTranslation
import OAI.Analysis.KadisonKastler.CoreTraceVectorTracial
import OAI.Analysis.KadisonKastler.CoreTraceMonomialReduction

namespace OAI

/-! # Trace symmetry on the bounded-frequency corner of the constructed core -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem constructedCore_traceSymmetry
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) :
    regularFrequencyWindow 0 1 * T * regularFrequencyWindow 0 1 ∈
      coreTraceSymmetrySpace
        (regularCoreConjugation (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc)
          (tomitaPolarConjugation J Ω hsep hcyc)) (coreTraceFrequencyVector Ω) := by
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  let R := regularCoreAlgebra U hU M
  let P := tomitaPolarConjugation J Ω hsep hcyc
  have hP := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have hPU := modularStrongGroup_polar_commutes J Ω hsep hcyc
  let C := regularCoreConjugation U hU P
  have hC := regularCoreConjugation_involutive U hU P hP hPU
  let p := regularFrequencyWindow (H := H) 0 1
  let ξ := coreTraceFrequencyVector Ω
  have hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω := by
    intro s
    simpa only [ofAdd_toAdd] using modularStrongGroup_fixes_state J Ω hsep hcyc s.toAdd
  have hPΩ := tomitaPolarConjugation_fixes_vector J Ω hsep hcyc
  have hCξ : C ξ = ξ := regularCoreConjugation_traceVector_fixed U hU P Ω hΩ hPΩ
  have hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M := by
    intro s a ha
    have he := modularStrongGroup_normalizes J Ω hsep hcyc s
    change unitaryConj (U s) a ∈ (M : Set (H →L[ℂ] H))
    rw [← he]
    exact Set.mem_image_of_mem _ ha
  have hCR : conjugateRightAlgebra C hC R = R.commutant :=
    regularCoreConjugation_commutant U hU P hP hPU M
      (tomitaPolarConjugation_commutant_eq J Ω hsep hcyc) hn
  have hright (a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (ha : a ∈ R) :
      conjugationOperator C a ∈ R.commutant := by
    rw [← hCR]
    exact ⟨a, ha, rfl⟩
  have hp : p ∈ R := regularFrequencyWindow_mem_core U hU M 0 1
  have hpstar : IsSelfAdjoint p := (regularFrequencyWindow_isStarProjection (H := H) 0 1).isSelfAdjoint
  have hp2 : p * p = p := (regularFrequencyWindow_isStarProjection (H := H) 0 1).isIdempotentElem.eq
  have hpξ : p ξ = ξ := coreTraceFrequencyVector_fixed Ω
  apply coreTraceSymmetry_of_monomials U hU M hn C ξ p ?_ T hT
  intro a ha s
  let A := p * regularCoreEmbedding U hU a * p
  let B := p * (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * p
  have hAmem : A ∈ R := R.mul_mem (R.mul_mem hp (regularCoreEmbedding_mem_core U hU M ha)) hp
  have hρmem := regularTranslation_mem_core U hU M s
  have hBmem : B ∈ R := R.mul_mem (R.mul_mem hp hρmem) hp
  have hA : A ∈ coreTraceSymmetrySpace C ξ := by
    apply coreTraceSymmetry_of_vector C hC ξ
    exact coreTraceEmbedding_vector_symmetry J Ω hsep hcyc ⟨a, ha⟩
  have hpρ := regularFrequencyWindow_commute_translation (H := H) 0 1 s
  have hB : B ∈ coreTraceSymmetrySpace C ξ := by
    apply coreTraceSymmetry_compress C hC ξ hCξ p _ hpstar hpξ hpρ.symm
    · exact VonNeumannAlgebra.mem_commutant_iff.mp (hright p hp) _ hρmem
    · exact coreTraceTranslation_vector_symmetry U hU P hP hPU Ω hΩ hPΩ s
  have hAB := coreTraceSymmetry_mul C hC ξ hCξ A B hA hB
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright (star B) (R.star_mem' hBmem)) A hAmem)
  have he : A * B = p * regularCoreMonomial U hU a s * p := by
    let ρ : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    change (p * regularCoreEmbedding U hU a * p) * (p * ρ * p) =
      p * (regularCoreEmbedding U hU a * ρ) * p
    calc
      _ = p * regularCoreEmbedding U hU a * (p * p) * ρ * p := by noncomm_ring
      _ = p * regularCoreEmbedding U hU a * (p * ρ) * p := by rw [hp2]; noncomm_ring
      _ = p * regularCoreEmbedding U hU a * (ρ * p) * p := by rw [hpρ.eq]
      _ = p * (regularCoreEmbedding U hU a * ρ) * (p * p) := by noncomm_ring
      _ = _ := by rw [hp2]
  rwa [he] at hAB

/-- The weighted packet is tracial on its supported corner. -/
theorem constructedCore_corner_tracial
    (A B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hA : A ∈ regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)
    (hB : B ∈ regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)
    (hpA : regularFrequencyWindow 0 1 * A = A)
    (hAp : A * regularFrequencyWindow 0 1 = A)
    (hpB : regularFrequencyWindow 0 1 * B = B)
    (hBp : B * regularFrequencyWindow 0 1 = B) :
    inner ℂ (coreTraceFrequencyVector Ω) ((A * B) (coreTraceFrequencyVector Ω)) =
      inner ℂ (coreTraceFrequencyVector Ω) ((B * A) (coreTraceFrequencyVector Ω)) := by
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  let P := tomitaPolarConjugation J Ω hsep hcyc
  let C := regularCoreConjugation U hU P
  have hC := regularCoreConjugation_involutive U hU P
    (tomitaPolarConjugation_involutive J Ω hsep hcyc)
    (modularStrongGroup_polar_commutes J Ω hsep hcyc)
  have ha := constructedCore_traceSymmetry J Ω hsep hcyc A hA
  have hb := constructedCore_traceSymmetry J Ω hsep hcyc B hB
  rw [hpA, hAp] at ha
  rw [hpB, hBp] at hb
  exact coreTraceSymmetry_tracial C hC (coreTraceFrequencyVector Ω) A B ha hb

end

end KadisonKastler

end OAI
