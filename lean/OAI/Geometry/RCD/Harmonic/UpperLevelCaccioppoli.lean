import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli

namespace OAI

/-! # Harmonic energy estimates above an arbitrary nonnegative level -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Testing above a level sees the same energy pairing before and after
positive-part truncation. This is locality on the zero set of the test. -/
theorem upper_level_cutoff_energy_eq
    (u : SobolevSpace μ hQ) {k : ℝ} (hk : 0 ≤ k)
    {χ : X → ℝ} {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x) :
    let v := u.upperPositivePart μ hQ hk
    let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
    energyForm μ hQ v (M (M v)) = energyForm μ hQ u (M (M v)) := by
  intro v M
  let test := M (M v)
  have hΓ : localGamma μ hQ v test =ᵐ[μ] localGamma μ hQ u test := by
    filter_upwards [localGamma_upperPositivePart μ hQ u test hk,
      u.upperPositivePart_coe μ hQ hk,
      SobolevSpace.cutoffCLM_coe μ hQ hχ hs hb hn v,
      SobolevSpace.cutoffCLM_coe μ hQ hχ hs hb hn (M v),
      localGamma_zero_on_level μ hQ test u 0,
      localGamma_comm μ hQ u test] with x hp hv hM hM2 hz hc
    change localGamma μ hQ v test x = _ at hp
    change SobolevSpace.toLp μ hQ v x = _ at hv
    change SobolevSpace.toLp μ hQ (M v) x = _ at hM
    change SobolevSpace.toLp μ hQ test x = _ at hM2
    by_cases hx : k < SobolevSpace.toLp μ hQ u x
    · simpa only [ite_eq_left hx] using hp
    · have hv0 : SobolevSpace.toLp μ hQ v x = 0 := by
        rw [hv,upperLevelPart,max_eq_right (by linarith)]
      have ht0 : SobolevSpace.toLp μ hQ test x = 0 := by rw [hM2,hM,hv0,mul_zero,mul_zero]
      rw [hp,ite_eq_right hx,hc,hz ht0]
  rw [← integral_localGamma_eq_energyForm,integral_congr_ae hΓ,
    integral_localGamma_eq_energyForm]

/-- The actual unbounded upper-level part of a harmonic function satisfies
the weighted energy estimate. Compact cutoff multiplication supplies the test. -/
theorem IsSobolevHarmonicOn.upper_level_caccioppoli
    {Ω : Set X} (u η : SobolevSpace μ hQ) {k : ℝ} (hk : 0 ≤ k)
    (hharm : IsSobolevHarmonicOn μ hQ Ω u)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hΩ : tsupport χ ⊆ Ω) (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A) :
    let v := u.upperPositivePart μ hQ hk
    (∫ x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ v x)^2 ∂μ) ≤
      4*∫ x, (SobolevSpace.toLp μ hQ v x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  intro v
  let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
  let test := M (M v)
  have hmem : test ∈ SobolevSpace.dirichlet μ hQ Ω :=
    SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hχ hs hb hn hΩ (M v)
  have he : energyForm μ hQ v test = 0 := by
    rw [upper_level_cutoff_energy_eq μ hQ u hk hχ hs hb hn]
    exact hharm test hmem
  exact caccioppoli_cutoffCLM μ hQ v η hχ hs hb hn hrep hgrad he

end RegularPointCoordinates

end

end OAI
