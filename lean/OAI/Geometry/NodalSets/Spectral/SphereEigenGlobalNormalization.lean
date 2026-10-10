import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive
import OAI.Geometry.NodalSets.Spectral.SphereEigenGlobalRepresentative

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] sphereGlobalRepresentativeMeasurable sphereGlobalRepresentativeBorel

theorem sphere_L2_representative_pairing (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (u : Base → ℝ) (ha : u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ)) :
    sphereWeightedPairing d.density u u=‖f‖^2 := by
  rw [sphereWeightedPairing,sphereWeightedL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(sphereWeightedMeasure_ae_iff d _).mp ha] with x hx
  rw [hx]
  ring

theorem sphere_eigen_global_normalized (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (heigen : sphereL2Resolvent d f=mu • f) (hn : ‖f‖=1) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) ∧
      sphereWeightedPairing d.density u u=1 ∧ u ≠ 0 ∧
      ∀ p x, x ∈ interior (Yau.realCenteredCube 4 (1/64)) →
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) (u ∘ sphereChartCoordMap p)) x+
          sphereEigenForcingCoefficient d p mu x*u (sphereChartCoordMap p x)=0 := by
  obtain ⟨u,hu,ha,he⟩ := sphere_eigen_global_representative d hrho mu hmu f heigen
  have hnorm : sphereWeightedPairing d.density u u=1 := by
    rw [sphere_L2_representative_pairing d f u ha,hn,one_pow]
  refine ⟨u,hu,ha,hnorm,?_,he⟩
  intro hz
  simp only [hz,sphereWeightedPairing,Pi.zero_apply,mul_zero,integral_zero] at hnorm
  norm_num at hnorm

end
end Yau.Target

end OAI
