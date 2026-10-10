import OAI.Analysis.CircleDomains.Rigidity.PrincipalScalarSolver
import OAI.Analysis.CircleDomains.Rigidity.ConductivityEnergy

namespace OAI

/-! Retain the constructed compact scalar transport when deriving the
principal conductivity energy identity. -/
open Set Filter Function MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_principal_conductivity_energy_scalar
    (hsolver : PrincipalConductivityScalarSolver)
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
          2*Real.pi*c.re ∧ CompactScalarPullback φ := by
  obtain ⟨φ, D, ht, hsys, hscalar⟩ := hsolver F hF n (by omega)
  have hh := D.conductivity_holomorphic_off φ.continuous hF.isClosed n hsys
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
  exact ⟨φ, D, c, T, hT, ht, hexp, hsys, hh, hI, hE, hscalar⟩

end CircleDomainRigidity

end

end OAI
