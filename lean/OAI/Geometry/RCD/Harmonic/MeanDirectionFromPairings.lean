import OAI.Geometry.RCD.Sobolev.MeanGradient
import OAI.Geometry.RCD.Coordinates.NormalizedPairing
import OAI.Geometry.RCD.Harmonic.AffineCenterBounds
import OAI.Geometry.RCD.Harmonic.LocalL2Restriction

namespace OAI

/-! # Recovering the mean gradient from constant-direction pairings -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The constant-direction L2 estimate controls the actual averaged
coordinate gradient. This is the bridge from the two-center commutator
estimate to coefficient recovery in directional pinching. -/
theorem meanGradientVector_error_of_pairings
    (U H : E →L[ℝ] SobolevSpace μ hQ) (f : SobolevSpace μ hQ)
    (s : Set X) (hs : MeasurableSet s) (hfin : μ s ≠ ∞) (hpos : μ s ≠ 0)
    (δ : E) {D : ℝ} (hD : 0 ≤ D)
    (hrep : ∀ b, SobolevSpace.toLp μ hQ (H b) =ᵐ[μ.restrict s]
      localGamma μ hQ f (U b))
    (herror : ∀ b, ‖normalizeLocalL2 μ s hfin
      (SobolevSpace.restrictLp μ hQ s (H b) - ⟪δ, b⟫_ℝ • restrictedOne μ s hfin)‖ ≤ D * ‖b‖) :
    ‖meanGradientVector μ hQ U s hs f - δ‖ ≤ D := by
  let : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hv : 0 < μ.real s := ENNReal.toReal_pos hpos hfin
  have hone : ‖normalizeLocalL2 μ s hfin (restrictedOne μ s hfin)‖ = 1 := by
    simpa only [one_smul, abs_one] using normalized_constant_norm μ s hfin hpos 1
  have hinner (b : E) :
      ⟪normalizeLocalL2 μ s hfin
          (SobolevSpace.restrictLp μ hQ s (H b) - ⟪δ, b⟫_ℝ • restrictedOne μ s hfin),
        normalizeLocalL2 μ s hfin (restrictedOne μ s hfin)⟫_ℝ =
      ⟪meanGradientVector μ hQ U s hs f - δ, b⟫_ℝ := by
    rw [normalized_inner]
    have heq : (∫ x in s,
        (SobolevSpace.restrictLp μ hQ s (H b) - ⟪δ, b⟫_ℝ • restrictedOne μ s hfin) x *
          restrictedOne μ s hfin x ∂μ) =
        ∫ x in s, localGamma μ hQ f (U b) x - ⟪δ, b⟫_ℝ ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (SobolevSpace.restrictLp μ hQ s (H b))
          (⟪δ, b⟫_ℝ • restrictedOne μ s hfin),
        Lp.coeFn_smul ⟪δ, b⟫_ℝ (restrictedOne μ s hfin),
        SobolevSpace.restrictLp_coe μ hQ s (H b), hrep b, restrictedOne_coe μ s hfin]
        with x hsub hsmul hr hp ho
      simp only [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hr, hp, ho,
        mul_one]
    rw [heq, integral_sub (localGamma_memL1 μ hQ f (U b)).integrableOn (integrable_const _),
      integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
      mul_sub, ← meanGradientVector_inner μ hQ U s hs f b, inner_sub_left]
    congr 1
    field_simp [hv.ne']
  have hbound (b : E) : |⟪meanGradientVector μ hQ U s hs f - δ, b⟫_ℝ| ≤ D * ‖b‖ := by
    rw [← hinner]
    apply (abs_real_inner_le_norm _ _).trans
    rw [hone, mul_one]
    exact herror b
  let a := meanGradientVector μ hQ U s hs f - δ
  have hb := hbound a
  change |⟪a, a⟫_ℝ| ≤ D * ‖a‖ at hb
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hb
  by_contra hn
  have hlt : D < ‖a‖ := lt_of_not_ge hn
  have hapos : 0 < ‖a‖ := lt_of_le_of_lt hD hlt
  have hm := mul_lt_mul_of_pos_right hlt hapos
  nlinarith

end RegularPointCoordinates

end

end OAI
