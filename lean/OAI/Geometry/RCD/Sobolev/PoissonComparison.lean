import OAI.Geometry.RCD.Sobolev.PoissonReplacement
import OAI.Geometry.RCD.Sobolev.DirichletMaximum

namespace OAI

/-! # Comparison for the constant-Laplacian Dirichlet replacement -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A distributional upper Laplacian bound on the boundary datum makes
its constant-Laplacian replacement lie below it. This is the comparison
used for the squared-distance datum in the Poisson pinching argument. -/
theorem constant_laplacian_replacement_le (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (c : ℝ) (u v : SobolevSpace μ hQ)
    (hboundary : v - u ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ v φ.val = -c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    (hcomparison : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) →
      -energyForm μ hQ u φ.val ≤ c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ v x ≤ SobolevSpace.toLp μ hQ u x := by
  let F := dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin c) +
    (sobolevEnergyForm μ hQ u).comp (SobolevSpace.dirichlet μ hQ Ω).subtypeL
  have hF (φ : SobolevSpace.dirichlet μ hQ Ω) :
      F φ = c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ +
        energyForm μ hQ u φ.val := by
    change dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin c) φ + _ = _
    rw [dirichletSource_indicator]
    rfl
  have hFpos (φ : SobolevSpace.dirichlet μ hQ Ω)
      (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) : 0 ≤ F φ := by
    rw [hF]
    linarith [hcomparison φ hφ]
  let h : SobolevSpace.dirichlet μ hQ Ω :=
    ⟨u - v, by simpa only [neg_sub] using
      (SobolevSpace.dirichlet μ hQ Ω).neg_mem hboundary⟩
  have hh (φ : SobolevSpace.dirichlet μ hQ Ω) :
      energyForm μ hQ h.val φ.val = F φ := by
    change energyForm μ hQ (u - v) φ.val = F φ
    rw [energyForm_sub_left, hsolve, hF]
    ring
  have hp := dirichlet_solution_nonneg μ hQ Ω hP hbound F hFpos h hh
  filter_upwards [hp, Lp.coeFn_sub (SobolevSpace.toLp μ hQ u)
    (SobolevSpace.toLp μ hQ v)] with x hx hsub
  change 0 ≤ SobolevSpace.toLp μ hQ (u - v) x at hx
  rw [map_sub, hsub, Pi.sub_apply] at hx
  exact sub_nonneg.mp hx

/-- Existence and the comparison conclusion are obtained together from
coercivity and the actual distributional Laplacian inequality. -/
theorem exists_constant_laplacian_replacement_le
    (Ω : Set X) (hΩ : MeasurableSet Ω) (hfin : μ Ω ≠ ∞)
    {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (c : ℝ) (u : SobolevSpace μ hQ)
    (hcomparison : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) →
      -energyForm μ hQ u φ.val ≤ c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) :
    ∃ v : SobolevSpace μ hQ, v - u ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        energyForm μ hQ v φ.val = -c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) ∧
      (∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ v x ≤ SobolevSpace.toLp μ hQ u x) := by
  obtain ⟨v, hv, hs⟩ := exists_constant_laplacian_replacement μ hQ Ω hΩ hfin hP hbound c u
  exact ⟨v, hv, hs, constant_laplacian_replacement_le μ hQ Ω hΩ hfin hP hbound
    c u v hv hs hcomparison⟩

end RegularPointCoordinates

end

end OAI
