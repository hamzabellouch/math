import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartNormalField

namespace OAI

/-! Pull a local normal field in the phase coordinates back to the surface.
The result is smooth, unit length and normal on its actual chart domain. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseNormalLift (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (n : SmallModes.Base → NormalFrame.Vec) : M → Space :=
  fun p => spaceCoordinates.symm (n (baseEquiv (e (chart (i : M) p))))

theorem phaseNormalLift_properties (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {U : Set SmallModes.Base} {W : Set M} {n : SmallModes.Base → NormalFrame.Vec}
    (hn : ContDiffOn ℝ ∞ n U) (hnunit : ∀ x ∈ U, n x ⬝ᵥ n x = 1)
    (hnnormal : ∀ x ∈ U, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n x = 0)
    (hW : W ⊆ (chart (i : M)).source)
    (hWe : MapsTo (chart (i : M)) W e.source)
    (hWU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) W U)
    (houter : ∀ p ∈ W, A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ)) :
    ContMDiffOn planeModel spaceModel ∞ (A.phaseNormalLift i e n) W ∧
      (∀ p ∈ W, ‖A.phaseNormalLift i e n p‖ = 1) ∧
      ∀ p ∈ W, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential F p v) (A.phaseNormalLift i e n p) = 0 := by
  have hcoord : ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞
      (fun p => baseEquiv (e (chart (i : M) p))) W :=
    (baseEquiv.contDiff.comp he).contMDiff.comp_contMDiffOn ((chart_smooth (i : M)).mono hW)
  have hlift := spaceCoordinates.symm.contDiff.contMDiff.comp_contMDiffOn
    (hn.contMDiffOn.comp hcoord hWU)
  refine ⟨hlift,?_,?_⟩
  · intro p hp
    exact norm_coordinate_inverse_of_dot_self (hnunit _ (hWU hp))
  · intro p hp v
    exact A.phase_chart_normal_of_outer i hF e he hi (hW hp) (houter p hp) (hWe hp)
      (n (baseEquiv (e (chart (i : M) p)))) (hnnormal _ (hWU hp)) v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
