import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Geometry.ConstantNormBoundaryGeometry

namespace OAI

/-! Initial inward radial positivity in every fixed nonlinear phase chart.
It supplies the whole-curve part of the finite boundary invariant. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

theorem spherical_second_positive {G : M → Space} {r : ℝ} (hr : 0 < r)
    (hunit : ∀ p, ‖G p‖ = 1) {g : SmoothMetric M}
    (hF : IsSmoothIsometricImmersion M g (r • G))
    {p : M} (hp : p ∈ c.carrier) :
    0 < c.second (r • G) p ⬝ᵥ spaceCoordinates (-G p) ∧
      c.second (r • G) p ≠ 0 ∧
      spaceCoordinates (-G p) ≠ -normalize (c.second (r • G) p) := by
  let H := surfacePhaseMap (c.index : M) c.phase (r • G)
  let x := c.coordinate p
  have hps : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hp
  have hx : x ∈ (surfacePhaseChart (c.index : M) c.phase).target :=
    (surfacePhaseChart (c.index : M) c.phase).map_source hps
  have hback : (surfacePhaseChart (c.index : M) c.phase).symm x = p :=
    (surfacePhaseChart (c.index : M) c.phase).left_inv hps
  have hg := B.phaseRealChartMap_surface_germ c.index c.phase (r • G) hx
    (by rw [hback]; exact c.active p hp)
  have hHs : ContDiffOn ℝ ∞ H (surfacePhaseChart (c.index : M) c.phase).target := by
    apply ContMDiffOn.contDiffOn
    exact spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn
      (hF.1.comp_contMDiffOn (surfacePhaseChart_symm_smooth (c.index : M) c.phase c.inverse_smooth))
  have hR : ∀ y, H y ⬝ᵥ H y = r^2 := by
    intro y
    simp only [H,surfacePhaseMap,Function.comp_apply,Pi.smul_apply,spaceCoordinates_dot]
    rw [real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,hunit,mul_one,sq_abs]
  have hD : gramDet (coordDeriv dx H x) (coordDeriv dy H x) ≠ 0 := by
    change gramDet (fderiv ℝ H x dx) (fderiv ℝ H x dy) ≠ 0
    rw [← hg.fderiv_eq]
    exact B.phase_gram_at_source c.index c.phase c.smooth c.inverse_smooth hF (c.source hp) (c.active p hp)
  have hh := constant_norm_boundary_geometry (surfacePhaseChart (c.index : M) c.phase).open_target
    hHs hR hr hx (injective_of_gramDet_ne_zero _ hD) (show (dy : SmallModes.Base) ≠ 0 by simp [dy])
  have hrad : r⁻¹ • (-H x) = spaceCoordinates (-G p) := by
    change r⁻¹ • (-spaceCoordinates ((r • G) ((surfacePhaseChart (c.index : M) c.phase).symm x))) = _
    rw [hback]
    simp only [Pi.smul_apply,map_smul,map_neg,smul_neg,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  rw [hrad] at hh
  have hsec : c.second (r • G) p = realSecondForm H dy dy x :=
    (c.second_eq (r • G) hp).trans (realSecondForm_eventuallyEq hg dy dy).eq_of_nhds
  rw [hsec]
  refine ⟨hh.1,hh.2.1,?_⟩
  intro hbad
  apply hh.2.2
  simp only [hbad,neg_neg]

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
