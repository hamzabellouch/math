import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingTail
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousQuotientDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeEquation

namespace OAI

/-! # Actual outgoing channels divided by the matched profile -/

open Set Filter Topology Asymptotics MeasureTheory
open scoped ContDiff

namespace DefocusingNLS
open ProfileCertificate
local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem canonical_position_derivatives
    (ν eta M : ℂ) (m : ℕ) (L : ℝ) (c : ℂ × ℂ)
    (Y : ℂ → ℝ → V₄) (hY : IsCanonicalHolomorphicColumn ν eta M m L c Y)
    (lam : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (Y lam s).1.1) (Y lam t).1.2 t ∧
      HasDerivAt (fun s => (Y lam s).2.1) (Y lam t).2.2 t := by
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t
    (hY.1 lam t ht)
  have hm := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t
    (hY.1 lam t ht)
  have hp' := homogeneousPair_fst_hasDerivAt hp
  have hm' := homogeneousPair_fst_hasDerivAt hm
  constructor
  · simpa only [ContinuousLinearMap.coe_fst', Function.comp_def,
      circularLeadingField, circularBoundedField, Prod.fst_add, zero_add] using hp'
  · simpa only [ContinuousLinearMap.coe_snd', Function.comp_def,
      circularLeadingField, circularBoundedField, Prod.fst_add, Prod.snd_add, zero_add] using hm'

private theorem quotient_combination_value
    (ν μ : ℂ) (Y Z Q : ℝ → ℂ × ℂ) (a b : ℂ) (r : ℝ) :
    (a * (spectralPhysicalJet (μ + ν) Y r).1 +
      b * (spectralPhysicalJet (μ + ν) Z r).1) /
      (Complex.exp (μ * (Real.log r : ℂ)) * (Q (Real.log r)).1) =
    (spectralQuotientJet ν (fun t => a • Y t + b • Z t) Q r).1 := by
  rw [add_div, mul_div_assoc, mul_div_assoc,
    homogeneousQuotient_value, homogeneousQuotient_value]
  simp only [spectralQuotientJet, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  ring

theorem homogeneous_matched_quotient_decay
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta lam : ℂ) (hlam : 4 ≤ lam.re)
    (F G : ℝ → ℂ) (Yp Ym : ℂ → ℝ → V₄)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1, 0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0, 1) Ym)
    (c : ℂ × ℂ) (R₀ : ℝ)
    (hstate : ∀ r, R₀ ≤ r → harmonicRadialState F G r =
      c.1 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Yp lam) r +
      c.2 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Ym lam) r) :
    let Q := radialMatchedEvenProfile n z
    ((fun r => F r / Q r) =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv (fun r => F r / Q r) =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ))) ∧
    ((fun r => G r / star (Q r)) =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv (fun r => G r / star (Q r)) =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ))) := by
  intro Q
  let ν := radialShootingNu (n + radialInnerShootingThreshold) z
  let W := radialExteriorCanonical ν (n + radialInnerShootingThreshold)
    (radialShootingM z) (Real.log innerBoundaryRadius)
  let Wm := fun t => (star (W t).1, star (W t).2)
  let P := fun t => c.1 • (Yp lam t).1 + c.2 • (Ym lam t).1
  let S := fun t => c.1 • (Yp lam t).2 + c.2 • (Ym lam t).2
  have hW := radialExteriorCanonical_spec hX
  have hM : radialShootingM z ≠ 0 := radialShootingM_ne_zero z
  have hWm : Tendsto Wm atTop (𝓝 (star (radialShootingM z), 0)) := by
    simpa only [Wm, W, ν, star_zero, Function.comp_def] using
      (continuous_star.continuousAt.tendsto.comp hW.2.1.tendsto.fst_nhds).prodMk_nhds
        (continuous_star.continuousAt.tendsto.comp hW.2.1.tendsto.snd_nhds)
  have hP : Tendsto P atTop (𝓝 (c.1, 0)) := by
    simpa only [P, Prod.fst, smul_zero, Prod.smul_mk, smul_eq_mul,
      mul_one, mul_zero, add_zero, zero_add, Prod.mk_add_mk] using
      ((hYp.2.1 lam).fst_nhds.const_smul c.1).add ((hYm.2.1 lam).fst_nhds.const_smul c.2)
  have hS : Tendsto S atTop (𝓝 (c.2, 0)) := by
    simpa only [S, Prod.snd, smul_zero, Prod.smul_mk, smul_eq_mul,
      mul_one, mul_zero, add_zero, zero_add, Prod.mk_add_mk] using
      ((hYp.2.1 lam).snd_nhds.const_smul c.1).add ((hYm.2.1 lam).snd_nhds.const_smul c.2)
  have hPd : ∀ᶠ t in atTop, HasDerivAt (fun s => (P s).1) (P t).2 t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change HasDerivAt (fun s => c.1 * (Yp lam s).1.1 + c.2 * (Ym lam s).1.1)
      (c.1 * (Yp lam t).1.2 + c.2 * (Ym lam t).1.2) t
    exact (((canonical_position_derivatives _ _ _ _ _ _ Yp hYp lam t ht).1).const_mul c.1).add
        (((canonical_position_derivatives _ _ _ _ _ _ Ym hYm lam t ht).1).const_mul c.2)
  have hSd : ∀ᶠ t in atTop, HasDerivAt (fun s => (S s).1) (S t).2 t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change HasDerivAt (fun s => c.1 * (Yp lam s).2.1 + c.2 * (Ym lam s).2.1)
      (c.1 * (Yp lam t).2.2 + c.2 * (Ym lam t).2.2) t
    exact (((canonical_position_derivatives _ _ _ _ _ _ Yp hYp lam t ht).2).const_mul c.1).add
        (((canonical_position_derivatives _ _ _ _ _ _ Ym hYm lam t ht).2).const_mul c.2)
  have hWd : ∀ᶠ t in atTop, HasDerivAt (fun s => (W s).1) (W t).2 t := by
    filter_upwards [eventually_ge_atTop (Real.log innerBoundaryRadius)] with t ht
    exact homogeneousPair_fst_hasDerivAt ((hW.2.2 t ht).2)
  have hWmd : ∀ᶠ t in atTop, HasDerivAt (fun s => (Wm s).1) (Wm t).2 t := by
    filter_upwards [hWd] with t ht
    exact ht.star
  have hν : (-2 * lam).re ≤ -8 := by
    norm_num [Complex.mul_re]
    linarith
  have hplus := homogeneousQuotient_energy_decay_of_limits (-2 * lam) hν P W
    (c.1, 0) (radialShootingM z) hM hP hW.2.1.tendsto hPd hWd
  have hminus := homogeneousQuotient_energy_decay_of_limits (-2 * lam) hν S Wm
    (c.2, 0) (star (radialShootingM z)) (star_ne_zero.mpr hM) hS hWm hSd hWmd
  have hQ (r : ℝ) (hr : innerBoundaryRadius < r) :
      Q r = Complex.exp (ν * (Real.log r : ℂ)) * (W (Real.log r)).1 := by
    dsimp only [Q]
    rw [radialMatchedEvenProfile_nonneg n z r (by linarith [innerBoundaryRadius_bounds.1])]
    simp only [radialMatchedProfile, ite_eq_right hr.not_ge,
      radialShootingExteriorProfile, radialPhysicalExterior, W, ν]
  have hQm (r : ℝ) (hr : innerBoundaryRadius < r) :
      star (Q r) = Complex.exp (star ν * (Real.log r : ℂ)) * (Wm (Real.log r)).1 := by
    rw [hQ r hr]
    simp only [star_mul, Wm, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
    ring
  have hep : (fun r => (spectralQuotientJet (-2 * lam) P W r).1) =ᶠ[atTop]
      (fun r => F r / Q r) := by
    filter_upwards [eventually_ge_atTop R₀, eventually_gt_atTop innerBoundaryRadius] with r hr hri
    have hs := congrArg (fun v : V₄ => v.1.1) (hstate r hr)
    change F r = _ at hs
    rw [hs, hQ r hri]
    simpa only [P, ν, spectralPhysicalPair, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
      sub_eq_add_neg, neg_mul] using
      (quotient_combination_value (-2 * lam) ν (fun t => (Yp lam t).1)
        (fun t => (Ym lam t).1) W c.1 c.2 r).symm
  have hem : (fun r => (spectralQuotientJet (-2 * lam) S Wm r).1) =ᶠ[atTop]
      (fun r => G r / star (Q r)) := by
    filter_upwards [eventually_ge_atTop R₀, eventually_gt_atTop innerBoundaryRadius] with r hr hri
    have hs := congrArg (fun v : V₄ => v.2.1) (hstate r hr)
    change G r = _ at hs
    rw [hs, hQm r hri]
    simpa only [S, ν, spectralPhysicalPair, Prod.snd_add, Prod.smul_snd, Prod.fst_add,
      Prod.smul_fst, smul_eq_mul, sub_eq_add_neg, neg_mul] using
      (quotient_combination_value (-2 * lam) (star ν) (fun t => (Yp lam t).2)
        (fun t => (Ym lam t).2) Wm c.1 c.2 r).symm
  exact ⟨homogeneousComplexEnergyDecay_congr hep hplus.1 hplus.2.1,
    homogeneousComplexEnergyDecay_congr hem hminus.1 hminus.2.1⟩

end DefocusingNLS

end OAI
