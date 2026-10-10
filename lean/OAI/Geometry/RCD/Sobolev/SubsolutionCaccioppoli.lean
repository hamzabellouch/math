import OAI.Geometry.RCD.Sobolev.WeakSubsolution

namespace OAI

/-! # Upper-level Caccioppoli estimate with a zeroth-order term -/

open Set Filter MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The potential term is retained explicitly, allowing the level-set
iteration to use the same cutoff energy estimate as in the harmonic case. -/
theorem IsWeakSubsolutionOn.upper_level_caccioppoli
    {Ω : Set X} (u η : SobolevSpace μ hQ) {a k : ℝ} (hk : 0 ≤ k)
    (hu : IsWeakSubsolutionOn μ hQ Ω u a)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hΩ : tsupport χ ⊆ Ω) (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A) :
    let v := u.upperPositivePart μ hQ hk
    (∫ x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ v x)^2 ∂μ) ≤
      2*a*(∫ x, (SobolevSpace.toLp μ hQ η x)^2*SobolevSpace.toLp μ hQ u x*
        SobolevSpace.toLp μ hQ v x ∂μ)+
      4*(∫ x, (SobolevSpace.toLp μ hQ v x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) := by
  intro v
  let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
  let test := M (M v)
  have hmem : test ∈ SobolevSpace.dirichlet μ hQ Ω :=
    SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hχ hs hb hn hΩ (M v)
  have hval : SobolevSpace.toLp μ hQ test =ᵐ[μ] fun x =>
      (χ x)^2*SobolevSpace.toLp μ hQ v x := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hχ hs hb hn (M v),
      SobolevSpace.cutoffCLM_coe μ hQ hχ hs hb hn v] with x h1 h2
    change SobolevSpace.toLp μ hQ test x = _ at h1
    change SobolevSpace.toLp μ hQ (M v) x = _ at h2
    rw [h1,h2]
    ring
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ test x := by
    filter_upwards [hval,u.upperPositivePart_coe μ hQ hk] with x ht hv
    change SobolevSpace.toLp μ hQ v x = _ at hv
    rw [ht,hv]
    exact mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hweak := hu ⟨test,hmem⟩ hnonneg
  have hI : inner ℝ (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ test) =
      ∫ x, (SobolevSpace.toLp μ hQ η x)^2*SobolevSpace.toLp μ hQ u x*
        SobolevSpace.toLp μ hQ v x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hval,hrep] with x ht hη
    rw [ht,hη,Real.inner_apply]
    ring
  change energyForm μ hQ u test ≤ a*inner ℝ (SobolevSpace.toLp μ hQ u)
    (SobolevSpace.toLp μ hQ test) at hweak
  rw [hI] at hweak
  have heq := upper_level_cutoff_energy_eq μ hQ u hk hχ hs hb hn
  change energyForm μ hQ v test = energyForm μ hQ u test at heq
  have he := caccioppoli_cutoffCLM_energy μ hQ v η hχ hs hb hn hrep hgrad
  change _ ≤ 2*energyForm μ hQ v test+4*(∫ x, (SobolevSpace.toLp μ hQ v x)^2*
    (SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ) at he
  rw [heq] at he
  linarith only [he,hweak]

end RegularPointCoordinates

end

end OAI
