import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWeyl
import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm
import OAI.Analysis.CircleDomains.Selection.ExteriorDecay
import OAI.Analysis.CircleDomains.Topology.HomeomorphicCoordinateRange

namespace OAI

/-! The constructed principal conductivity homeomorphism is holomorphic
off its coefficient support. Its principal Laurent germ and uniform
exterior decay follow from the proved local Weyl lemma. -/
open Set Filter Function MeasureTheory Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.conductivity_holomorphic_off
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hφ : Continuous φ) {F : Set EuclideanPlane} (hF : IsClosed F) (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ := by
  have hcr : ∀ᵐ x ∂volume, x ∈ Fᶜ →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0 := by
    filter_upwards [hsys] with x hx hxF
    simpa only [conductivityValue, ite_eq_right hxF, one_mul, neg_mul, one_mul] using hx
  have hh := D.holomorphic_on_of_cauchyRiemann (hφ.comp complexPlaneCoordinates.continuous)
    hF.isOpen_compl hcr
  simpa only [ContinuousLinearEquiv.apply_symm_apply,
    image_compl_eq complexPlaneCoordinates.bijective] using hh

 theorem exists_principal_conductivity_holomorphic (hprincipal : PrincipalRealBeltrami)
    {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z-z) (cobounded ℂ) (𝓝 0) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) ∧
      DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ ∧
      (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨φ, D, ht, hsys⟩ := exists_principal_conductivity_coordinate hprincipal hF n hn
  have hh := D.conductivity_holomorphic_off φ.continuous hF.isClosed n hsys
  have hclosed := (hF.image complexPlaneCoordinates.continuous).isClosed
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ φ z := by
    have hmem : ∀ᶠ z in cobounded ℂ, z ∈ (complexPlaneCoordinates '' F)ᶜ := by
      rw [Metric.cobounded_eq_cocompact]
      exact (hF.image complexPlaneCoordinates.continuous).compl_mem_cocompact
    exact hmem.mono fun z hz => hh.differentiableAt (hclosed.isOpen_compl.mem_nhds hz)
  exact ⟨φ, D, ht, hsys, hh, principal_bigO_of_exterior_holomorphic hd ht⟩

 theorem principal_conductivity_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : Set EuclideanPlane}
    {φ : ℂ ≃ₜ ℂ} (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    (hnorm : (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    {R : ℝ} (hR : 0 < R) (hFR : complexPlaneCoordinates '' F ⊆ Metric.ball 0 R) :
    ∀ z : ℂ, 2*R ≤ ‖z‖ → ‖φ z-z‖ ≤ 2*R^2/‖z‖ := by
  have hext : {z : ℂ | R < ‖z‖} ⊆ (complexPlaneCoordinates '' F)ᶜ := by
    intro z hz hzF
    have hzR := hFR hzF
    have hlt : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hzR
    exact (not_lt_of_ge hz.le) hlt
  exact harea.scaled_exterior_decay hR (hh.mono hext) (φ.injective.injOn) hnorm

end CircleDomainRigidity

end

end OAI
