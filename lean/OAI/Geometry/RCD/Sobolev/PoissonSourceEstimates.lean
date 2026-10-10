import OAI.Geometry.RCD.Sobolev.PositiveDirichletFunctional
import OAI.Geometry.RCD.Sobolev.PoissonHeight
import OAI.Geometry.RCD.Sobolev.PoissonEnergyError

namespace OAI

/-!
# Positive-source estimates for the actual Poisson replacement

The positive Laplacian defect is specified on the boundary datum and compact
Lipschitz tests. Its action on the difference with the constructed replacement
is proved, then used for positivity, height and linear gradient estimates.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The Laplacian defect of the boundary datum is the positive source of
its difference with the constant-Laplacian replacement. -/
theorem replacement_has_measure_source (Ω : Set X) (q f : SobolevSpace μ hQ)
    (σ : Measure X) (a : ℝ)
    (hdefect : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ q ψ + a * (∫ x in Ω, v x ∂μ) = ∫ x, v x ∂σ)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ f φ.val = -a * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) :
    IsDirichletMeasureSource μ hQ Ω (q - f) σ := by
  intro ψ v C hv hvc hs hψ
  have hψmem : ψ ∈ SobolevSpace.dirichlet μ hQ Ω :=
    (SobolevSpace.dirichletCore μ hQ Ω).le_topologicalClosure ⟨v, C, hv, hvc, hs, hψ⟩
  have hf := hsolve ⟨ψ, hψmem⟩
  have he : (∫ x in Ω, SobolevSpace.toLp μ hQ ψ x ∂μ) = ∫ x in Ω, v x ∂μ :=
    integral_congr_ae (ae_restrict_of_ae hψ)
  rw [he] at hf
  rw [energyForm_sub_left, hf]
  linarith [hdefect ψ v C hv hvc hs hψ]

/-- The positive source on compact tests implies the full weak comparison
inequality used by the Dirichlet maximum principle. -/
theorem comparison_of_replacement_source (Ω : Set X) (q f : SobolevSpace μ hQ)
    (σ : Measure X) (a : ℝ)
    (hsource : IsDirichletMeasureSource μ hQ Ω (q - f) σ)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ f φ.val = -a * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    (φ : SobolevSpace.dirichlet μ hQ Ω)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) :
    -energyForm μ hQ q φ.val ≤ a * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ := by
  have hh := hsource.test_nonneg μ hQ Ω (q - f) σ φ hφ
  rw [energyForm_sub_left, hsolve] at hh
  linarith

variable [BorelSpace X] [ProperSpace X]

/-- The analytic Poisson bounds in fixed rescaled units, with constants
coming from torsion and the positive-source estimate. -/
theorem poisson_source_estimates (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) {P : ℝ} (hP : 0 ≤ P)
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val)
    (q f : SobolevSpace μ hQ) (Q : X → ℝ) {L : ℝ≥0}
    (hQlip : LipschitzWith L Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ] Q)
    {a B K A d C : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hd : 1 < d) (hC : 0 ≤ C)
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
    (hdefect : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ q ψ + a * (∫ x in Ω, v x ∂μ) = ∫ x, v x ∂σ)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val) :
    (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (q - f) x ∧
      SobolevSpace.toLp μ hQ (q - f) x ≤ B + a * K) ∧
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ (q - f) x) Ω μ ∧
    (∫ x in Ω, SobolevSpace.minimalSlope μ hQ (q - f) x ∂μ) ≤
      σ.real Ω * positiveSourceGradientBound (μ.real Ω) C d ((1 + d) / 2) ∧
    (∫ x, (SobolevSpace.minimalSlope μ hQ (q - f) x) ^ 2 ∂μ) ≤
      σ.real Ω * (B + a * K) ∧
    (∫ x in Ω, |(1 / 2 : ℝ) * localGamma μ hQ f f x -
      (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ) ≤
      (A * positiveSourceGradientBound (μ.real Ω) C d ((1 + d) / 2) +
        (B + a * K) / 2) * σ.real Ω := by
  have hsource := replacement_has_measure_source μ hQ Ω q f σ a hdefect hsolve
  have hcomp := comparison_of_replacement_source μ hQ Ω q f σ a hsource hsolve
  have hheight := poisson_replacement_height_le μ hQ Ω hΩ hfin hP hpoin q f Q
    hQlip hQ0 hq ha hB hK hQB τ hτ hτK hfq hsolve hcomp
  let H : SobolevSpace.dirichlet μ hQ Ω :=
    ⟨q - f, by simpa only [neg_sub] using (SobolevSpace.dirichlet μ hQ Ω).neg_mem hfq⟩
  have hheight0 : 0 ≤ B + a * K := add_nonneg hB (mul_nonneg ha hK)
  have hg := positive_source_bounds_of_measure μ hQ Ω hΩ hfin H σ hsource
    hd hC hheight0 hheight hsob
  have he := poisson_energy_density_error_le_source μ hQ Ω hΩ hfin q H σ hsource
    hd hC hheight0 hA hheight hgradq hsob
  have hident : q - H.val = f := by dsimp [H]; module
  rw [hident] at he
  exact ⟨hheight, hg.1, hg.2.1, hg.2.2, he⟩

end RegularPointCoordinates

end

end OAI
