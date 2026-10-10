import OAI.Analysis.KadisonKastler.WeightedStripCyclic
import OAI.Analysis.KadisonKastler.WeightedStripBoundary
import OAI.Analysis.KadisonKastler.ResolventSqrtCalculus

namespace OAI

/-! # The weighted strip boundaries are modular orbit operators -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem weightedStripOperator_right (t : ℝ) :
    weightedStripOperator (M := M) J Ω ((1 / 2 : ℂ) + t * Complex.I) =
      graphResolvent M J Ω 1 * (1 - graphResolvent M J Ω 1) ^ 3 *
        (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let r := resolventCoordinateFunction R
  let g := r * (1 - r) ^ 3
  have he := weightedStripOperator_eq_group J Ω hsep hcyc (1 / 2) t (by norm_num) g
    (fun s hs hs1 => by
      simpa only [g, r, resolventCoordinateFunction, ContinuousMap.mul_apply,
        ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
          weightedStripKernel_right hs hs1 t)
  have hg : resolventContinuousCalculus R hR g = R * (1 - R) ^ 3 := by
    dsimp [g, r]
    rw [map_mul, map_pow, map_sub, map_one, resolventContinuousCalculus_coordinate]
  change weightedStripOperator (M := M) J Ω _ = resolventContinuousCalculus R hR g * _ at he
  rw [hg] at he
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, hg] using he

theorem weightedStripOperator_left (t : ℝ) :
    weightedStripOperator (M := M) J Ω ((-1 / 2 : ℂ) + t * Complex.I) =
      graphResolvent M J Ω 1 ^ 2 * (1 - graphResolvent M J Ω 1) ^ 2 *
        (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let r := resolventCoordinateFunction R
  let g := r ^ 2 * (1 - r) ^ 2
  have he := weightedStripOperator_eq_group J Ω hsep hcyc (-1 / 2) t (by norm_num) g
    (fun s hs hs1 => by
      simpa only [g, r, resolventCoordinateFunction, ContinuousMap.mul_apply,
        ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
          weightedStripKernel_left hs hs1 t)
  have hg : resolventContinuousCalculus R hR g = R ^ 2 * (1 - R) ^ 2 := by
    dsimp [g, r]
    rw [map_mul, map_pow, map_pow, map_sub, map_one, resolventContinuousCalculus_coordinate]
  change weightedStripOperator (M := M) J Ω _ = resolventContinuousCalculus R hR g * _ at he
  rw [hg] at he
  simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_ofNat, hg] using he

end

end KadisonKastler

end OAI
