import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerInput
import OAI.Geometry.RCD.Harmonic.HarmonicCorrection

namespace OAI

/-!
# Weak radial cancellation and its harmonic correction

The local Hessian test formula is equation (3.1.10) in Gigli (2018).
The cancellation itself is proved here: constant Laplacian and harmonicity
make the two integration-by-parts terms vanish, and continuity extends the
identity from the regular test core to the actual Dirichlet space.
-/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Integrating a local gradient pairing with a zero-boundary function
gives the full Dirichlet pairing. Locality removes the complement. -/
theorem integral_localGamma_dirichlet (Ω : Set X) (hΩ : MeasurableSet Ω)
    (f : SobolevSpace μ hQ) (φ : SobolevSpace.dirichlet μ hQ Ω) :
    (∫ x in Ω, localGamma μ hQ f φ.val x ∂μ) = energyForm μ hQ f φ.val := by
  rw [← integral_localGamma_eq_energyForm]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  have hz := SobolevSpace.dirichlet_zero_off μ hQ Ω hΩ φ
  have hz' := (ae_restrict_iff' hΩ.compl).mp hz
  filter_upwards [hz', localGamma_zero_on_level μ hQ φ.val f 0,
    localGamma_comm μ hQ f φ.val] with x hx hlevel hcomm hnot
  rw [hcomm]
  exact hlevel (hx hnot)

/-- A local Hessian pairing with one fixed gradient. All functions in the
Koszul formula are genuine Sobolev functions. The regular test core is
dense in the zero-boundary Sobolev space. -/
structure LocalHessianPairing (Ω : Set X) (f a : SobolevSpace μ hQ) where
  mixed : SobolevSpace μ hQ
  mixed_rep : SobolevSpace.toLp μ hQ mixed =ᵐ[μ.restrict Ω] localGamma μ hQ f a
  core : Submodule ℝ (SobolevSpace.dirichlet μ hQ Ω)
  core_dense : Dense (core : Set (SobolevSpace.dirichlet μ hQ Ω))
  gammaF : core → SobolevSpace.dirichlet μ hQ Ω
  gammaA : core → SobolevSpace.dirichlet μ hQ Ω
  gammaF_rep : ∀ φ, SobolevSpace.toLp μ hQ (gammaF φ).val =ᵐ[μ]
    localGamma μ hQ f φ.val.val
  gammaA_rep : ∀ φ, SobolevSpace.toLp μ hQ (gammaA φ).val =ᵐ[μ]
    localGamma μ hQ a φ.val.val
  hessian : SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ
  koszul : ∀ φ, 2 * hessian φ.val =
    energyForm μ hQ a (gammaF φ).val + energyForm μ hQ φ.val.val mixed -
      energyForm μ hQ f (gammaA φ).val

namespace LocalHessianPairing

/-- The Hessian formula implies weak radial cancellation. -/
theorem weak_cancellation {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a)
    {c : ℝ} (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsSobolevHarmonicOn μ hQ Ω a)
    (b : ℝ) (φ : SobolevSpace.dirichlet μ hQ Ω) :
    energyForm μ hQ G.mixed φ.val =
      2 * (G.hessian φ - b * energyForm μ hQ a φ.val) := by
  let F := (sobolevEnergyForm μ hQ G.mixed).comp
    (SobolevSpace.dirichlet μ hQ Ω).subtypeL
  have heq : (F : SobolevSpace.dirichlet μ hQ Ω → ℝ) =
      (2 : ℝ) • G.hessian := by
    apply Continuous.ext_on G.core_dense F.continuous ((2 : ℝ) • G.hessian).continuous
    intro ψ hψ
    let t : G.core := ⟨ψ, hψ⟩
    have hia : (∫ x in Ω, SobolevSpace.toLp μ hQ (G.gammaA t).val x ∂μ) =
        energyForm μ hQ a ψ.val := by
      rw [integral_congr_ae (ae_restrict_of_ae (G.gammaA_rep t))]
      exact integral_localGamma_dirichlet μ hQ Ω hΩ a ψ
    have hz := hf (G.gammaA t).val (G.gammaA t).property
    rw [hia, ha ψ.val ψ.property, mul_zero] at hz
    have hk := G.koszul t
    rw [ha (G.gammaF t).val (G.gammaF t).property, hz,
      zero_add, sub_zero, energyForm_comm μ hQ ψ.val G.mixed] at hk
    exact hk.symm
  have hv := congrFun heq φ
  change energyForm μ hQ G.mixed φ.val = 2 * G.hessian φ at hv
  rw [ha φ.val φ.property, mul_zero, sub_zero]
  exact hv

/-- The shifted Hessian bound becomes a divergence defect bound with the
exact factor four from weak cancellation. -/
theorem energy_defect_le {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a)
    {c : ℝ} (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsSobolevHarmonicOn μ hQ Ω a) (b D : ℝ)
    (hbound : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (G.hessian φ - b * energyForm μ hQ a φ.val) ^ 2 ≤
        D * energyForm μ hQ φ.val φ.val)
    (φ : SobolevSpace.dirichlet μ hQ Ω) :
    (energyForm μ hQ G.mixed φ.val) ^ 2 ≤ (4 * D) * energyForm μ hQ φ.val φ.val := by
  rw [G.weak_cancellation μ hQ hΩ hf ha b φ]
  nlinarith [hbound φ]

/-- Lax--Milgram now constructs the harmonic approximation to the radial
derivative, with energy and L² error linear in the shifted Bochner mass. -/
theorem exists_harmonic_correction {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a)
    {c P D : ℝ} (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsSobolevHarmonicOn μ hQ Ω a) (b : ℝ) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hpoincare : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ φ.val‖ ^ 2 ≤ P * energyForm μ hQ φ.val φ.val)
    (hbound : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (G.hessian φ - b * energyForm μ hQ a φ.val) ^ 2 ≤
        D * energyForm μ hQ φ.val φ.val) :
    ∃ h : SobolevSpace μ hQ, G.mixed - h ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      IsSobolevHarmonicOn μ hQ Ω h ∧
      energyForm μ hQ (G.mixed - h) (G.mixed - h) ≤ 4 * D ∧
      ‖SobolevSpace.toLp μ hQ (G.mixed - h)‖ ^ 2 ≤ P * (4 * D) := by
  exact RegularPointCoordinates.exists_harmonic_correction μ hQ Ω hP
    (mul_nonneg (by norm_num) hD) hpoincare G.mixed (G.energy_defect_le μ hQ hΩ hf ha b D hbound)

end LocalHessianPairing
end RegularPointCoordinates

end

end OAI
