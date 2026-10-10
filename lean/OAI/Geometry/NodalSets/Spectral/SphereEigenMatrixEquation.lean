import OAI.Geometry.NodalSets.Elliptic.RealWeightedElliptic
import OAI.Geometry.NodalSets.Spectral.SphereEigenClassicalEquation

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_eigen_matrix_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x))) :
    ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
      Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x+
        sphereEigenForcingCoefficient d p mu x*v x=0 := by
  intro x hx
  have he := sphere_eigen_classical_equation d p hrho mu hmu f heigen v hv ha x hx
  have hid : Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x =
      ∑ a, ∑ j, Yau.coordPartial
        (fun y ↦ sphereChartPrincipalDensity d p y a j*Yau.coordPartial v y a) x j := by
    unfold Yau.coordDiv realMatrixFlux
    simp_rw [Yau.real_coordPartial_sum _ (fun a ↦
      (sphereChartPrincipalDensity_smooth d p _ a).mul (Yau.real_coordPartial_smooth v hv a))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext y
    rw [sphereChartPrincipalDensity_symmetric d p y j a]
  rw [hid]
  linarith only [he]

end
end Yau.Target

end OAI
