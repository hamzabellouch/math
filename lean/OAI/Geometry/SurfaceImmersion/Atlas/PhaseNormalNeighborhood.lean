import OAI.Geometry.SurfaceImmersion.Atlas.PhaseNormalLift
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetCoordinateRelation

namespace OAI

/-! The local exact normal defines a genuine smooth unit normal on an
open surface neighborhood of the closed primitive disk. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseNormalLift_coordinates (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (ν : SmallModes.Base → NormalFrame.Vec) (p : M) :
    spaceCoordinates (A.phaseNormalLift i e ν p) = ν (baseEquiv (e (chart (i : M) p))) :=
  spaceCoordinates.apply_symm_apply _

theorem phase_normal_neighborhood (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {U₀ : Set SmallModes.Base} (hU₀ : IsOpen U₀) {ν : SmallModes.Base → NormalFrame.Vec}
    (hν : ContDiffOn ℝ ∞ ν U₀) (hunit : ∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1)
    (hnormal : ∀ x ∈ U₀, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ ν x = 0)
    {K : Set M}
    (hKs : K ⊆ (chart (i : M)).source)
    (hKe : MapsTo (chart (i : M)) K e.source)
    (hKU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) K U₀)
    (hKw : ∀ p ∈ K, A.weight i p ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ U ⊆ (chart (i : M)).source ∧
      MapsTo (chart (i : M)) U e.source ∧
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) U U₀ ∧
      ContMDiffOn planeModel spaceModel ∞ (A.phaseNormalLift i e ν) U ∧
      (∀ p ∈ U, ‖A.phaseNormalLift i e ν p‖ = 1) ∧
      ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential F p v) (A.phaseNormalLift i e ν p) = 0 := by
  let V := e.source ∩ (fun x => baseEquiv (e x)) ⁻¹' U₀
  have hV : IsOpen V := e.open_source.inter
    (hU₀.preimage (baseEquiv.continuous.comp he.continuous))
  let U := ((chart (i : M)).source ∩ (chart (i : M)) ⁻¹' V) ∩ {p | A.weight i p ≠ 0}
  have hU : IsOpen U := ((chart (i : M)).isOpen_inter_preimage hV).inter
    (isOpen_ne.preimage (A.weight_smooth i).continuous)
  have hKU' : K ⊆ U := fun p hp => ⟨⟨hKs hp,⟨hKe hp,hKU hp⟩⟩,hKw p hp⟩
  have hUs : U ⊆ (chart (i : M)).source := fun _ hp => hp.1.1
  have hUe : MapsTo (chart (i : M)) U e.source := fun _ hp => hp.1.2.1
  have hUU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) U U₀ := fun _ hp => hp.1.2.2
  obtain ⟨hs,hu,hn⟩ := A.phaseNormalLift_properties i hF e he hi hν hunit hnormal hUs hUe hUU
    (fun p hp => A.outer_eventually_one_of_weight_ne_zero i hp.2)
  exact ⟨U,hU,hKU',hUs,hUe,hUU,hs,hu,hn⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
