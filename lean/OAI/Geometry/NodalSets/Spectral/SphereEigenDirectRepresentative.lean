import OAI.Geometry.NodalSets.Spectral.SphereEigenMatrixEquation

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_eigen_rescaled_input (d : SphereEnergyData) (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    sphereL2Resolvent d (mu⁻¹ • f)=f ∧
      sphereL2Resolvent d (mu⁻¹ • f)=mu • (mu⁻¹ • f) := by
  have hr : sphereL2Resolvent d (mu⁻¹ • f)=f := by
    rw [map_smul,heigen,smul_smul,inv_mul_cancel₀ hmu,one_smul]
  refine ⟨hr,?_⟩
  rw [hr,smul_smul,mul_inv_cancel₀ hmu,one_smul]

theorem sphere_eigen_direct_matrix_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ f (sphereChartCoordMap p x))) :
    ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
      Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x+
        sphereEigenForcingCoefficient d p mu x*v x=0 := by
  obtain ⟨hr,he⟩ := sphere_eigen_rescaled_input d mu hmu f heigen
  apply sphere_eigen_matrix_equation d p hrho mu hmu (mu⁻¹ • f) he v hv
  simpa only [hr] using ha

theorem sphere_eigen_direct_representative (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
      tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
      v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
        (fun x ↦ f (sphereChartCoordMap p x)) ∧
      ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x+
          sphereEigenForcingCoefficient d p mu x*v x=0 := by
  obtain ⟨hr,he⟩ := sphere_eigen_rescaled_input d mu hmu f heigen
  obtain ⟨v,hv,hs,ha⟩ := sphere_eigen_smooth_representative d p hrho mu hmu (mu⁻¹ • f) he
  rw [hr] at ha
  exact ⟨v,hv,hs,ha,sphere_eigen_direct_matrix_equation d p hrho mu hmu f heigen v hv ha⟩

end
end Yau.Target

end OAI
