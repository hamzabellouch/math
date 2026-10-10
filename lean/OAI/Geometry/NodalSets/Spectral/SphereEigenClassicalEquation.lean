import OAI.Geometry.NodalSets.Elliptic.RealLocalSmoothDerivativeLemmas
import OAI.Geometry.NodalSets.Spectral.SphereEigenSmoothQuantitative

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section

theorem sphere_eigen_smooth_gradient (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x))) (i : Fin 4) :
    (fun x ↦ Yau.coordPartial v x i) =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/64))]
      (sphereChartDerivativeMap d p i (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ) := by
  obtain ⟨K,hK,hjet⟩ := sphere_eigen_all_finite_weak_jets d p hrho mu hmu 0
  obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := hjet f heigen
  have h := Yau.real_interior_weak_restrict
    (Yau.realCenteredCube_isCompact 4 (1/32))
    (Yau.realCenteredCube_isCompact 4 (1/16)).measurableSet
    (Yau.realCenteredCube_mono (by norm_num))
    (U []) (U [i]) (hU [] (by simp)).1 (hU [i] (by simp)).1 i
    (fun psi hp hc hs ↦ (hw [] (by simp) i psi hp hc hs).2.2)
  have haU : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))] U [] := by rw [hzero]; exact ha
  have hid := Yau.real_local_smooth_derivative_ae
    (Yau.realCenteredCube_isCompact 4 (1/32)) (U []) (U [i]) v h.1 h.2.1 hv haU i
    (fun psi hp hc hs ↦ (h.2.2 psi hp hc hs).2.2)
  rw [hone i] at hid
  exact ae_mono (Measure.restrict_mono (Yau.realCenteredCube_subset_interior (by norm_num)) le_rfl) hid

theorem sphere_eigen_classical_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x))) :
    ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
      -(∑ a, ∑ j, Yau.coordPartial
        (fun y ↦ sphereChartPrincipalDensity d p y a j*Yau.coordPartial v y a) x j)=
        sphereEigenForcingCoefficient d p mu x*v x := by
  obtain ⟨K,hK,hjet⟩ := sphere_eigen_all_finite_weak_jets d p hrho mu hmu 0
  obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := hjet f heigen
  let Q := Yau.realCenteredCube 4 (1/64)
  have hgrad (a : Fin 4) : (fun x ↦ Yau.coordPartial v x a) =ᵐ[volume.restrict Q] U [a] := by
    rw [hone a]
    exact sphere_eigen_smooth_gradient d p hrho mu hmu f heigen v hv ha a
  have hvalue : v =ᵐ[volume.restrict Q] U [] := by
    rw [hzero]
    exact ae_mono (Measure.restrict_mono (Yau.realCenteredCube_mono (by norm_num)) le_rfl) ha
  have hB : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  apply Yau.real_smooth_divergence_equation (Yau.realCenteredCube_isCompact 4 (1/64))
    (fun a j y ↦ sphereChartPrincipalDensity d p y a j*Yau.coordPartial v y a)
    (fun a j ↦ (sphereChartPrincipalDensity_smooth d p a j).mul (Yau.real_coordPartial_smooth v hv a))
    (fun x ↦ sphereEigenForcingCoefficient d p mu x*v x) (hB.mul hv)
  intro psi hp hc hs
  have heq := Yau.real_weak_equation_restrict
    (Yau.realCenteredCube_isCompact 4 (1/16)).measurableSet
    (show Q ⊆ Yau.realCenteredCube 4 (1/16) from Yau.realCenteredCube_mono (by norm_num))
    (sphereChartPrincipalDensity d p) (fun a ↦ U [a])
    (fun x ↦ sphereEigenForcingCoefficient d p mu x*U [] x) hpde psi hp hc hs
  calc
    _ = ∑ a, ∑ j, ∫ x in Q,
        sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [hgrad a] with x hx
      rw [hx]
    _ = ∫ x in Q, sphereEigenForcingCoefficient d p mu x*U [] x*psi x := heq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hvalue] with x hx
      rw [hx]

end
end Yau.Target

end OAI
