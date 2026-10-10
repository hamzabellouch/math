import OAI.Analysis.KadisonKastler.RegularReflectedGauge
import OAI.Analysis.KadisonKastler.CoreTraceOriginalGauge
import OAI.Analysis.KadisonKastler.ConstructedCoreConjugation

namespace OAI

/-! # Trace-vector symmetry for compressed algebra generators -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCoreEmbedding_symmetry_of_balance
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (P : H ≃ₗᵢ⋆[ℂ] H)
    (hPU : ∀ s x, P ((U s : H →L[ℂ] H) x) = (U s : H →L[ℂ] H) (P x))
    (Ω : H) (hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω) (A : H →L[ℂ] H)
    (hbalance : regularFrequencyWindow 0 1
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket coreTraceFrequencyScalar (A Ω))) =
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyWindow 0 1
          ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
            (regularFrequencyPacket coreTraceFrequencyScalar (P ((star A) Ω)))))) :
    (regularFrequencyWindow 0 1 * regularCoreEmbedding U hU A * regularFrequencyWindow 0 1 :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (coreTraceFrequencyVector Ω) =
      regularCoreConjugation U hU P
        ((star (regularFrequencyWindow 0 1 * regularCoreEmbedding U hU A *
          regularFrequencyWindow 0 1 : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
          (coreTraceFrequencyVector Ω)) := by
  have hp := (regularFrequencyWindow_isStarProjection (H := H) 0 1).isSelfAdjoint.star_eq
  have hπ : star (regularCoreEmbedding U hU A) = regularCoreEmbedding U hU (star A) :=
    (map_star (regularCoreEmbedding U hU) A).symm
  simp only [star_mul, hp, hπ, mul_apply_eq_comp, coreTraceFrequencyVector_fixed]
  change regularFrequencyWindow 0 1
      (regularCoreEmbedding U hU A (regularFrequencyPacket coreTraceFrequencyScalar Ω)) =
    (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularReflectedConjugation P (regularFrequencyWindow 0 1
        (regularCoreEmbedding U hU (star A) (regularFrequencyPacket coreTraceFrequencyScalar Ω))))
  rw [regularCoreEmbedding_packet_fixed U hU Ω hΩ,
    regularCoreEmbedding_packet_fixed U hU Ω hΩ,
    regularReflectedConjugation_frequencyWindow,
    regularReflectedConjugation_gauge_star U hU P hPU,
    regularReflectedConjugation_real_packet P _ coreTraceFrequencyScalar_real]
  exact hbalance

variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem coreTraceEmbedding_vector_symmetry (a : Algebra M) :
    let U := modularStrongGroup J Ω hsep hcyc
    let hU := modularStrongGroup_continuous J Ω hsep hcyc
    let C := regularCoreConjugation U hU (tomitaPolarConjugation J Ω hsep hcyc)
    let p := regularFrequencyWindow (H := H) 0 1
    let ξ := coreTraceFrequencyVector Ω
    (p * regularCoreEmbedding U hU a.val * p) ξ =
      C ((star (p * regularCoreEmbedding U hU a.val * p)) ξ) := by
  have hΩ : ∀ s, (modularStrongGroup J Ω hsep hcyc s : H →L[ℂ] H) Ω = Ω := by
    intro s
    simpa only [ofAdd_toAdd] using modularStrongGroup_fixes_state J Ω hsep hcyc s.toAdd
  exact regularCoreEmbedding_symmetry_of_balance
    (modularStrongGroup J Ω hsep hcyc) (modularStrongGroup_continuous J Ω hsep hcyc)
    (tomitaPolarConjugation J Ω hsep hcyc) (modularStrongGroup_polar_commutes J Ω hsep hcyc)
    Ω hΩ a.val (coreTraceOriginal_gauge_balance J Ω hsep hcyc a)

end

end KadisonKastler

end OAI
