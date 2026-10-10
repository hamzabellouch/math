import OAI.Geometry.RCD.Sobolev.CutoffLevelVariation
import OAI.Geometry.RCD.Harmonic.UpperLevelCaccioppoli

namespace OAI

/-! # Localized heat energy above a level

The squared positive part has an L² derivative at every level. Locality
identifies its square-cutoff test with the original heat equation, so
the local energy estimate holds for every nonnegative level.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_level_cutoff_norm_hasDerivAt (f : Lp ℝ 2 μ)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    {k : ℝ} (hk : 0 ≤ k) (t : ℝ) (ht : 0 < t) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
    let u := heatSobolev μ hQ t ht f
    let v := u.upperPositivePart μ hQ hk
    HasDerivAt (fun s => ‖N (P (heatAt μ hQ s f))‖^2)
      (-2*energyForm μ hQ v (M (M v))) t := by
  intro N P M u v
  have hd := (cutoff_level_square_hasFDerivAt μ hχ hb hk (heatAt μ hQ t f)).comp_hasDerivAt t
    (heatAt_hasDerivAt μ hQ t ht f)
  have he : inner ℝ (N (N (P (heatAt μ hQ t f)))) (heatGeneratorAt μ hQ t f) =
      energyForm μ hQ v (M (M v)) := by
    calc
      _ = energyForm μ hQ u (M (M v)) := by
        rw [real_inner_comm,heatGeneratorAt_of_pos μ hQ t ht]
        exact (heatGenerator_form μ hQ t ht f (M (M v))).symm
      _ = _ := (upper_level_cutoff_energy_eq μ hQ u hk hχ hs hb hn).symm
  change HasDerivAt (fun s => ‖N (P (heatAt μ hQ s f))‖^2)
    (2*inner ℝ (N (N (P (heatAt μ hQ t f)))) (-heatGeneratorAt μ hQ t f)) t at hd
  simpa only [inner_neg_right,he,mul_neg,neg_mul] using hd

theorem heat_level_cutoff_energy_differential (f : Lp ℝ 2 μ) (η : SobolevSpace μ hQ)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A)
    {k : ℝ} (hk : 0 ≤ k) (t : ℝ) (ht : 0 < t) :
    let N := lpMultiplier μ (boundedMultiplier μ χ hχ.continuous.measurable B hb)
    let P := (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
    let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
    let v := (heatSobolev μ hQ t ht f).upperPositivePart μ hQ hk
    deriv (fun s => ‖N (P (heatAt μ hQ s f))‖^2) t+
        (1/2:ℝ)*energyForm μ hQ (M v) (M v) ≤
      5*∫ x, (P (heatAt μ hQ t f) x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  intro N P M v
  rw [(heat_level_cutoff_norm_hasDerivAt μ hQ f hχ hs hb hn hk t ht).deriv]
  have hc := caccioppoli_cutoffCLM_energy μ hQ v η hχ hs hb hn hrep hgrad
  have hp := energy_cutoffCLM_le μ hQ v η hχ hs hb hn hrep hgrad
  change energyForm μ hQ (M v) (M v) ≤ _ at hp
  change _ ≤ 2*energyForm μ hQ v (M (M v))+_ at hc
  change _ ≤ _+4*∫ x, (P (heatAt μ hQ t f) x)^2*
    (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ at hc
  change _ ≤ _+2*∫ x, (P (heatAt μ hQ t f) x)^2*
    (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ at hp
  linarith only [hc,hp]

end RegularPointCoordinates

end

end OAI
