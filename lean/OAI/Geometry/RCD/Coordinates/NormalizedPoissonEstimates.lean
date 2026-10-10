import OAI.Geometry.RCD.Coordinates.NormalizedSourceGradient
import OAI.Geometry.RCD.Sobolev.PoissonSourceEstimates

namespace OAI

/-! # Scale-correct source and energy estimates for Poisson replacement -/

open Set MeasureTheory Filter
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The normalized Sobolev inequality yields a linear gradient error, a
mass-times-height energy error, and the corresponding energy-density error. -/
theorem normalized_poisson_source_estimates (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) (hvol : 0 < μ.real Ω) {P : ℝ} (hP : 0 ≤ P)
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val)
    (q f : SobolevSpace μ hQ) (Q : X → ℝ) {L : ℝ≥0}
    (hQlip : LipschitzWith L Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ] Q)
    {a B K A d C s : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hd : 1 < d) (hC : 0 < C) (hs : 0 < s)
    (hQB : ∀ᵐ x ∂μ.restrict Ω, Q x ≤ B)
    (hgradq : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ hQ q x ≤ A)
    (τ : SobolevSpace.dirichlet μ hQ Ω)
    (hτ : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ τ.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    (hτK : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ τ.val x ≤ K)
    (hfq : f - q ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ f φ.val = -a * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hdefect : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (D : ℝ≥0),
      LipschitzWith D v → HasCompactSupport v → tsupport v ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ q ψ + a * (∫ x in Ω, v x ∂μ) = ∫ x, v x ∂σ)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        (C * s * (μ.real Ω) ^ (1 / d - 1)) * energyForm μ hQ φ.val φ.val) :
    let D := Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C * s)
    (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (q - f) x ∧
      SobolevSpace.toLp μ hQ (q - f) x ≤ B + a * K) ∧
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ (q - f) x) Ω μ ∧
    (∫ x in Ω, SobolevSpace.minimalSlope μ hQ (q - f) x ∂μ) ≤ σ.real Ω * D ∧
    (∫ x, (SobolevSpace.minimalSlope μ hQ (q - f) x) ^ 2 ∂μ) ≤ σ.real Ω * (B + a * K) ∧
    (∫ x in Ω, |(1 / 2 : ℝ) * localGamma μ hQ f f x -
      (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ) ≤
        (A * D + (B + a * K) / 2) * σ.real Ω := by
  dsimp only
  let D := Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C * s)
  have hsource := replacement_has_measure_source μ hQ Ω q f σ a hdefect hsolve
  have hcomp := comparison_of_replacement_source μ hQ Ω q f σ a hsource hsolve
  have hheight := poisson_replacement_height_le μ hQ Ω hΩ hfin hP hpoin q f Q
    hQlip hQ0 hq ha hB hK hQB τ hτ hτK hfq hsolve hcomp
  let H : SobolevSpace.dirichlet μ hQ Ω :=
    ⟨q - f, by simpa only [neg_sub] using (SobolevSpace.dirichlet μ hQ Ω).neg_mem hfq⟩
  have ht (φ : SobolevSpace.dirichlet μ hQ Ω) (t : ℝ) (ht : 0 ≤ t)
      (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧
        SobolevSpace.toLp μ hQ φ.val x ≤ t) :
      energyForm μ hQ H.val φ.val ≤ σ.real Ω * t :=
    hsource.bounded_test_bound μ hQ Ω H.val σ hΩ φ ht hφ
  have hg := normalized_source_gradient μ hQ Ω hfin hvol H
    (hheight.mono fun _ hx => hx.1) (q := (1 + d) / 2)
    (by linarith) (by linarith) hC hs measureReal_nonneg hsob ht
  have hheight0 : 0 ≤ B + a * K := add_nonneg hB (mul_nonneg ha hK)
  have he := positive_source_energy μ hQ Ω H hheight0 hheight ht
  have hsq : Integrable (fun x => (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2) μ :=
    (localGamma_memL1 μ hQ H.val H.val).congr (localGamma_self μ hQ H.val)
  have he' : (∫ x in Ω, (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 ∂μ) ≤
      σ.real Ω * (B + a * K) :=
    (setIntegral_le_integral hsq (Eventually.of_forall fun _ => sq_nonneg _)).trans he
  refine ⟨hheight, hg.1, hg.2, he, ?_⟩
  have hident : q - H.val = f := by dsimp only [H]; module
  have herr := poisson_energy_density_error_le μ hQ Ω q H.val hgradq hg.1
  rw [hident] at herr
  calc
    _ ≤ A * (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) +
        (1 / 2 : ℝ) * ∫ x in Ω, (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 ∂μ := herr
    _ ≤ A * (σ.real Ω * D) + (1 / 2 : ℝ) * (σ.real Ω * (B + a * K)) :=
      add_le_add (mul_le_mul_of_nonneg_left hg.2 hA)
        (mul_le_mul_of_nonneg_left he' (by norm_num))
    _ = _ := by dsimp only [D]; ring

end RegularPointCoordinates

end

end OAI
