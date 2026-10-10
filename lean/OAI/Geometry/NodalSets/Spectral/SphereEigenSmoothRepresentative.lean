import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealCubeCutoffs
import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakJetsSmooth
import OAI.Geometry.NodalSets.Spectral.SphereEigenAllFiniteWeakJets

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff Topology
noncomputable section

theorem sphere_eigen_cutoff_smooth (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior (Yau.realCenteredCube 4 (1/16)))
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
      tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
      v =ᵐ[volume] (fun x ↦ eta x*(sphereL2Resolvent d f) (sphereChartCoordMap p x)) := by
  apply Yau.real_local_weak_jets_smooth
    (Yau.realCenteredCube_isCompact 4 (1/16)) (Yau.realCenteredCube_isCompact 4 (1/8))
    eta he hc hs (hs.trans (interior_subset.trans (Yau.realCenteredCube_subset_interior (by norm_num))))
  intro N
  obtain ⟨K,hK,h⟩ := sphere_eigen_all_finite_weak_jets d p hrho mu hmu N
  obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := h f heigen
  refine ⟨U,hzero,fun es hh ↦ (hU es (by omega)).1,?_⟩
  intro es hh i psi hp hc hs
  exact (hw es (by omega) i psi hp hc hs).2.2

theorem sphere_eigen_smooth_representative (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
      tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
      v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
        (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) := by
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Yau.real_cube_smooth_cutoff (1/32) (3/64) (by norm_num)
  obtain ⟨v,hv,hsv,ha⟩ := sphere_eigen_cutoff_smooth d p hrho mu hmu eta he hc
    (hs.trans (Yau.realCenteredCube_subset_interior (by norm_num))) f heigen
  refine ⟨v,hv,hsv,?_⟩
  filter_upwards [ae_restrict_of_ae ha,
    self_mem_ae_restrict (Yau.realCenteredCube_isCompact 4 (1/32)).measurableSet] with x hx hxQ
  rw [hx,(h1 x hxQ).eq_of_nhds,one_mul]

end
end Yau.Target

end OAI
