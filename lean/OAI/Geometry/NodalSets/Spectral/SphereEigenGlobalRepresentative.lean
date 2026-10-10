import OAI.Geometry.NodalSets.Charts.SphereChartScalarExtension
import OAI.Geometry.NodalSets.Charts.SphereL2LocalPullback
import OAI.Geometry.NodalSets.Charts.SphereSmallChartPartition
import OAI.Geometry.NodalSets.Spectral.SphereEigenDirectRepresentative

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Filter Yau.Geometry
open scoped ContDiff Topology
noncomputable section
local instance sphereGlobalRepresentativeMeasurable : MeasurableSpace Base := borel Base
local instance sphereGlobalRepresentativeBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_eigen_global_representative (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) ∧
      ∀ p x, x ∈ interior (Yau.realCenteredCube 4 (1/64)) →
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) (u ∘ sphereChartCoordMap p)) x+
          sphereEigenForcingCoefficient d p mu x*u (sphereChartCoordMap p x)=0 := by
  classical
  obtain ⟨P,theta,htheta,hpos,hsum,hsupp,hpull,hcompact⟩ :=
    sphere_finite_smooth_partition_radius (1/128) (by norm_num)
  choose W hW hsW haW heW using (fun p : {p // p ∈ P} ↦
    sphere_eigen_direct_representative d p.val (hrho p.val) mu hmu f heigen)
  have hWcompact (p : {p // p ∈ P}) : HasCompactSupport (W p) :=
    (Yau.realCenteredCube_isCompact 4 (1/8)).of_isClosed_subset (isClosed_tsupport _) (hsW p)
  choose F hF hsF hFW using (fun p : {p // p ∈ P} ↦
    sphere_chart_scalar_extension p.val (W p) (hW p) (hWcompact p))
  let u : Base → ℝ := fun x ↦ ∑ p, theta p x*F p x
  have hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u :=
    ContMDiff.sum (fun p _ ↦ (htheta p).mul (hF p))
  have hlocal (p : {p // p ∈ P}) :
      (fun x ↦ theta p x*F p x) =ᵐ[sphereWeightedMeasure d.density] (fun x ↦ theta p x*f x) := by
    apply (sphereWeightedMeasure_ae_chart_iff d p.val _).mpr
    have he := (ae_restrict_iff' (Yau.realCenteredCube_isCompact 4 (1/32)).measurableSet).mp (haW p)
    filter_upwards [he] with x hx
    by_cases hz : theta p (sphereChartCoordMap p.val x)=0
    · simp only [hz,zero_mul]
    · have hxs : x ∈ ball (0 : Yau.Jets.Coord) (1/128) := by
        obtain ⟨z,hz',hez⟩ := hsupp p (subset_closure hz)
        exact (sphereChartCoordMap_injective p.val hez) ▸ hz'
      have hxQ : x ∈ Yau.realCenteredCube 4 (1/32) := by
        intro i _
        have hi : |x i| < (1/128:ℝ) := by
          have hh := (norm_le_pi_norm x i).trans_lt
            (show ‖x‖ < 1/128 from by simpa only [mem_ball,dist_zero_right] using hxs)
          simpa only [Real.norm_eq_abs] using hh
        constructor <;> linarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
      rw [hFW p x,hx hxQ]
  have hua : u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) := by
    filter_upwards [Filter.eventually_all.mpr hlocal] with x hx
    dsimp only [u]
    simp_rw [hx]
    rw [← Finset.sum_mul,hsum,one_mul]
  refine ⟨u,hu,hua,?_⟩
  intro p
  have huc : ContDiff ℝ ∞ (u ∘ sphereChartCoordMap p) :=
    (hu.comp (sphereChartCoordMap_smooth p)).contDiff
  apply sphere_eigen_direct_matrix_equation d p (hrho p) mu hmu f heigen _ huc
  exact ae_restrict_of_ae ((sphereWeightedMeasure_ae_chart_iff d p _).mp hua)

end
end Yau.Target

end OAI
