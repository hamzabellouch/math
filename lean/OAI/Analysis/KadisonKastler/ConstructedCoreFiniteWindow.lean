import OAI.Analysis.KadisonKastler.ConstructedCoreTraceSymmetry
import OAI.Analysis.KadisonKastler.CoreFrequencyFinite

namespace OAI

/-! # A finite nonzero projection in the constructed modular core -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem constructedCore_unitWindow_finite :
    let U := modularStrongGroup J Ω hsep hcyc
    let hU := modularStrongGroup_continuous J Ω hsep hcyc
    FiniteProjectionIn (regularCoreAlgebra U hU M)
      (unitCoreFrequencyProjection U hU M).val := by
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  have hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M := by
    intro s a ha
    have he := modularStrongGroup_normalizes J Ω hsep hcyc s
    change unitaryConj (U s) a ∈ (M : Set (H →L[ℂ] H))
    rw [← he]
    exact Set.mem_image_of_mem _ ha
  have hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω := by
    intro s
    simpa only [ofAdd_toAdd] using modularStrongGroup_fixes_state J Ω hsep hcyc s.toAdd
  apply unitCoreFrequencyProjection_finite_of_norm U hU M hn Ω hΩ hsep
  intro a hpa hap
  let P := tomitaPolarConjugation J Ω hsep hcyc
  let C := regularCoreConjugation U hU P
  have hC := regularCoreConjugation_involutive U hU P
    (tomitaPolarConjugation_involutive J Ω hsep hcyc)
    (modularStrongGroup_polar_commutes J Ω hsep hcyc)
  have ha := constructedCore_traceSymmetry J Ω hsep hcyc a.val a.property
  have hl : regularFrequencyWindow 0 1 * a.val = a.val := congrArg Subtype.val hpa
  have hr : a.val * regularFrequencyWindow 0 1 = a.val := congrArg Subtype.val hap
  rw [hl, hr] at ha
  exact coreTraceSymmetry_norm C hC (coreTraceFrequencyVector Ω) a.val ha

theorem constructedFactorialCore_projectionSemifinite [Nontrivial H]
    (hfactor : ScalarCenter (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)) :
    let R := regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M
    ∀ p : AlgebraProjection R, p.val ≠ 0 →
      ∃ q : AlgebraProjection R, q ≤ p ∧ q.val ≠ 0 ∧ FiniteProjectionIn R q.val := by
  exact projectionSemifinite_of_finite_projection hfactor
    (unitCoreFrequencyProjection _ _ M) (unitCoreFrequencyProjection_ne_zero _ _ M)
    (constructedCore_unitWindow_finite J Ω hsep hcyc)

end

end KadisonKastler

end OAI
