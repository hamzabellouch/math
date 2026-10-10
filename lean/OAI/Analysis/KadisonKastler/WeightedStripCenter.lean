import OAI.Analysis.KadisonKastler.WeightedStripOperatorBoundary

namespace OAI

/-! # The middle value of the weighted spectral strip -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hsep hcyc in
theorem weightedStripOperator_center :
    weightedStripOperator (M := M) J Ω 0 =
      graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1) ^ 2 *
        tomitaMiddleOperator (M := M) J Ω := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let r := resolventCoordinateFunction R
  let g := r * (1 - r) ^ 2 *
    (resolventSqrtFunction R * resolventComplementSqrtFunction R)
  have he := weightedStripOperator_eq_group J Ω hsep hcyc 0 0 (by norm_num) g
    (fun s hs hs1 => by
      simpa [g, r, resolventCoordinateFunction, resolventSqrtFunction,
        resolventComplementSqrtFunction, modularSpectralPhase] using
          weightedStripKernel_center hs hs1)
  have hp : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (graphResolvent_positive J Ω 1)
  have hq : 0 ≤ 1 - R := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    have hs := (tomitaGraphComplementRoot_nonneg (M := M) J Ω).isSelfAdjoint
    simpa only [hs.star_eq] using
      (star_mul_self_nonneg (tomitaGraphComplementRoot (M := M) J Ω))
  have hg : resolventContinuousCalculus R hR g = R * (1 - R) ^ 2 *
      tomitaMiddleOperator (M := M) J Ω := by
    dsimp [g, r]
    rw [map_mul, map_mul, map_mul, map_pow, map_sub, map_one,
      resolventContinuousCalculus_coordinate,
      resolventContinuousCalculus_sqrt R hR hp,
      resolventContinuousCalculus_complement_sqrt R hR hq]
    rfl
  change weightedStripOperator (M := M) J Ω _ = resolventContinuousCalculus R hR g * _ at he
  rw [hg] at he
  simpa only [Complex.ofReal_zero, zero_mul, zero_add, show Multiplicative.ofAdd (0 : ℝ) = 1 from rfl,
    map_one, OneMemClass.coe_one, mul_one, hg] using he

end

end KadisonKastler

end OAI
