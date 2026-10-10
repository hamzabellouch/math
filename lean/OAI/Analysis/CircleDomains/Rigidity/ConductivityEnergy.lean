import OAI.Analysis.CircleDomains.Rigidity.ConductivityJacobianLimit
import OAI.Analysis.CircleDomains.Rigidity.ConductivityGlobalEnergy

namespace OAI

/-! The exact global conductivity energy identity follows from the
constructed principal solution and the proved boundary limits. No area,
flux or energy estimate is an additional input. -/
open Set Filter Function MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.conductivity_energy_of_principal_expansion
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀)
    {c : ℂ} {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹)
    (n : ℕ) (hn : 2 ≤ n)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
    (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) +
      ((n : ℝ)-1)*(∫ x in F, (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) =
        2*Real.pi*c.re :=
  D.conductivity_global_energy hF n (by omega) c.re hsys
    (D.jacobian_area_limit hgreen hφ hF hh hr₀ hFr hT hexp)
    (D.vertical_flux_limit hgreen hφ hF hh hr₀ hFr hT.continuousAt hexp)

 theorem exists_principal_conductivity_energy (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) {F : Set EuclideanPlane}
    (hF : IsCompact F) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
      (c : ℂ) (T : ℂ → ℂ),
      AnalyticAt ℂ T 0 ∧
      Tendsto (fun z => φ z-z) (cobounded ℂ) (𝓝 0) ∧
      (∀ z : ℂ, z ≠ 0 → φ z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) ∧
      DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ ∧
      Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
      (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) +
        ((n : ℝ)-1)*(∫ x in F, (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) =
          2*Real.pi*c.re := by
  obtain ⟨φ, D, ht, hsys, hh, _hbig⟩ :=
    exists_principal_conductivity_holomorphic hprincipal hF n (by omega)
  have hFc := hF.image complexPlaneCoordinates.continuous
  have hdiff : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ φ z := by
    have hmem : ∀ᶠ z in cobounded ℂ, z ∈ (complexPlaneCoordinates '' F)ᶜ := by
      rw [Metric.cobounded_eq_cocompact]
      exact hFc.compl_mem_cocompact
    exact hmem.mono fun z hz => hh.differentiableAt (hFc.isClosed.isOpen_compl.mem_nhds hz)
  obtain ⟨c, T, hT, hexp⟩ := principal_exterior_expansion hdiff ht
  obtain ⟨R, hFR⟩ := hF.isBounded.subset_ball (0 : EuclideanPlane)
  have hr₀ : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFr₀ : F ⊆ ball 0 (max R 1) := hFR.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨hI, hE⟩ := D.conductivity_energy_of_principal_expansion hgreen φ.continuous
    hF hh hr₀ hFr₀ hT hexp n hn hsys
  exact ⟨φ, D, c, T, hT, ht, hexp, hsys, hh, hI, hE⟩

end CircleDomainRigidity

end

end OAI
