import OAI.Geometry.SurfaceImmersion.Atlas.PhaseOuterImmersion

namespace OAI

/-! Convert the prescribed metric's convexity and the chosen outer plateau
into all geometric hypotheses of the supported primitive loop. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates JetPolynomial SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem primitive_outer_geometry (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {phi : SmallModes.Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (realPhaseChart e x).1 = phi x)
    {T Ω : Set SmallModes.Base} (hΩ : IsOpen Ω) (hTΩ : T ⊆ Ω)
    (hΩe : Ω ⊆ (surfacePhaseChart (i : M) e).target)
    (houter : ∀ x ∈ T, A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1))
    (hconvex : ∀ x ∈ Ω, ∀ v : SmallModes.Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (i : M)) phi
        (coordinateChart (i : M) ((surfacePhaseChart (i : M) e).symm x)) v v) :
    ∃ U : Set SmallModes.Base, IsOpen U ∧ T ⊆ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ (n.inPhase (i : M) e) U ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x)) ∧
      (∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 ∧
        coordDeriv dy (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 ∧
        n.inPhase (i : M) e x ⬝ᵥ n.inPhase (i : M) e x = 1) ∧
      ∀ x ∈ U, 0 < coordinateMetricHessian
        (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F)) Prod.fst x dy dy := by
  obtain ⟨U,hU,hTU,hUΩ,ho⟩ := A.phase_outer_neighborhood i e hΩ hTΩ hΩe houter
  let E := surfacePhaseChart (i : M) e
  have hUE : U ⊆ E.target := hUΩ.trans hΩe
  refine ⟨U,hU,hTU,hUΩ,(n.inPhase_smooth (i : M) e hi).mono hUE,?_,?_,?_⟩
  · intro x hx
    have hp := E.map_target (hUE hx)
    have hh := A.phase_injective_of_outer i hF e he hi hp (ho x hx)
    change Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) (E (E.symm x))) at hh
    rwa [E.right_inv (hUE hx)] at hh
  · intro x hx
    exact ⟨A.preferred_normal_in_phase_of_outer i hF.1 n e hi (hUE hx) (ho x hx) dx,
      A.preferred_normal_in_phase_of_outer i hF.1 n e hi (hUE hx) (ho x hx) dy,
      n.inPhase_unit (i : M) e x⟩
  · intro x hx
    have hh := A.phase_hessian_positive_of_outer i hF e he hi hphi hphase
      (E.map_target (hUE hx)) (ho x hx) (hconvex x (hUΩ hx))
    change 0 < coordinateMetricHessian _ Prod.fst (E (E.symm x)) dy dy at hh
    rwa [E.right_inv (hUE hx)] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
