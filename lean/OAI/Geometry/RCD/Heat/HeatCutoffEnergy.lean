import OAI.Geometry.RCD.Sobolev.CutoffProductEnergy
import OAI.Analysis.RCDHeat.WeightedHilbert

namespace OAI

/-! # Local energy inequality for the actual heat flow

The cutoff operator acts on both L² and the actual Sobolev space. Its
self-adjointness identifies the time derivative with the admissible
square-cutoff test. No bound on the initial heat datum is used.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_cutoff_norm_hasDerivAt (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (t : ℝ) (ht : 0 < t) :
    let V := boundedMultiplier μ χ hχ.continuous.measurable B hb
    let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
    let u := heatSobolev μ hQ t ht f
    HasDerivAt (fun s => ‖lpMultiplier μ V (heatAt μ hQ s f)‖^2)
      (-2*energyForm μ hQ u (M (M u))) t := by
  intro V M u
  have hd := ((lpMultiplier μ V).hasFDerivAt.comp_hasDerivAt t
    (heatAt_hasDerivAt μ hQ t ht f)).norm_sq
  have he : inner ℝ (lpMultiplier μ V (heatAt μ hQ t f))
      (lpMultiplier μ V (heatGeneratorAt μ hQ t f)) =
      energyForm μ hQ u (M (M u)) := by
    rw [lpMultiplier_inner_symm, real_inner_comm,
      heatGeneratorAt_of_pos μ hQ t ht]
    exact (heatGenerator_form μ hQ t ht f (M (M u))).symm
  simpa only [Function.comp_apply, map_neg, inner_neg_right, he, mul_neg, neg_mul] using hd

omit [ProperSpace X] [μ.Regular] in
theorem cutoff_L2_norm_sq (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hb : ∀ x, |χ x| ≤ B) :
    ‖lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb) f‖^2 =
      ∫ x, χ x^2*f x^2 ∂μ := by
  rw [← integral_sq_Lp]
  apply integral_congr_ae
  filter_upwards [lpMultiplier_coe μ
    (boundedMultiplier μ χ hχ.continuous.measurable B hb) f,
    boundedMultiplier_coe μ χ hχ.continuous.measurable B hb] with x hx hχx
  rw [hx,hχx,mul_pow]

/-- The differential local energy inequality, with the cutoff error kept
as a localized integral. -/
theorem heat_cutoff_energy_differential (f : Lp ℝ 2 μ) (η : SobolevSpace μ hQ)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A)
    (t : ℝ) (ht : 0 < t) :
    let V := boundedMultiplier μ χ hχ.continuous.measurable B hb
    let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
    let u := heatSobolev μ hQ t ht f
    deriv (fun s => ‖lpMultiplier μ V (heatAt μ hQ s f)‖^2) t+
        (1/2:ℝ)*energyForm μ hQ (M u) (M u) ≤
      5*∫ x, (heatAt μ hQ t f x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  intro V M u
  rw [(heat_cutoff_norm_hasDerivAt μ hQ f hχ hs hb hn t ht).deriv]
  have hc := caccioppoli_cutoffCLM_energy μ hQ u η hχ hs hb hn hrep hgrad
  have hp := energy_cutoffCLM_le μ hQ u η hχ hs hb hn hrep hgrad
  change energyForm μ hQ (M u) (M u) ≤ _ at hp
  change _ ≤ 2*energyForm μ hQ u (M (M u))+_ at hc
  simp only [u,heatSobolev_toLp] at hc hp
  linarith only [hc,hp]

end RegularPointCoordinates

end

end OAI
