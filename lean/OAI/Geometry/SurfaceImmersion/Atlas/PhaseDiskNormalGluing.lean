import OAI.Geometry.SurfaceImmersion.Atlas.PhaseNormalNeighborhood
import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormalDiskGluing
import OAI.Geometry.SurfaceImmersion.Atlas.ImmersedAtlasNormal

namespace OAI

/-! Glue the constructed exact phase normal to the actual exterior
projection, producing the global preferred normal required by a primitive step. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates NormalFrame VelocityFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_disk_normal_gluing_within (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (hn : ContMDiff planeModel spaceModel ∞ n)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (O : Set M) (hO : IsOpen O)
    {D : Set M} (hD : IsOpen D) (hfO : frontier D ⊆ O)
    {U₀ : Set SmallModes.Base} (hU₀ : IsOpen U₀) {ν : SmallModes.Base → Vec}
    (hν : ContDiffOn ℝ ∞ ν U₀) (hunit : ∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1)
    (hnormal : ∀ x ∈ U₀, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ ν x = 0)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (hproj : ∀ p ∉ D, A.projectedNormalField F n p ≠ 0)
    (hanti : ∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField F n p) ≠
      -ν (baseEquiv (e (chart (i : M) p))))
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, Continuous (B k))
    (hin : ∀ k p, p ∈ C k → p ∈ D →
      ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize (B k p))
    (hout : ∀ k p, p ∈ C k → p ∉ closure D →
      spaceCoordinates (A.unitProjectedNormalField F n p) ≠ -normalize (B k p))
    (hpair : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < B k p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
      0 < B k p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField F n p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ W ⊆ O ∧ ∃ N : PreferredNormal F,
      (∀ p ∈ D \ W, N.vector p = A.phaseNormalLift i e ν p) ∧
      (∀ p ∈ (closure D)ᶜ \ W, N.vector p = A.unitProjectedNormalField F n p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨U,hU,hDU',_,_,_,ha,haunit,hanormal⟩ :=
    A.phase_normal_neighborhood i hF e he hi hU₀ hν hunit hnormal hDs hDe hDU hDw
  let V := {p | A.projectedNormalField F n p ≠ 0}
  have hgram := fun (j : A.centers) (x : SmallModes.Base) (hx : x ∈ tsupport (A.planeWeight j)) =>
    A.planeWeight_gram_of_immersion hF hI houter j hx
  have hV : IsOpen V := isOpen_ne.preimage (A.projectedNormalField_smooth hF hn hgram).continuous
  have hDV : Dᶜ ⊆ V := hproj
  obtain ⟨hb,hbunit,hbnormal⟩ := A.unitProjectedNormalField_properties hF hn hgram
    (show ∀ p ∈ V, A.projectedNormalField F n p ≠ 0 from fun _ hp => hp)
  apply preferredNormal_disk_gluing_within O hO hfO hD hU hV hDU' hDV ha hb haunit hbunit hanormal hbnormal
    ?_ C hC B (fun k => (hB k).continuousOn) ?_ hout ?_
  · intro p hp heq
    apply hanti p hp
    have h := congrArg spaceCoordinates heq
    simpa only [map_neg,A.phaseNormalLift_coordinates] using h
  · intro k p hp hpd
    rw [A.phaseNormalLift_coordinates]
    exact hin k p hp hpd
  · intro k p hp hpf
    have hh := hpair k p hp hpf
    constructor
    · rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply,A.phaseNormalLift_coordinates]
      exact hh.1
    · rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply]
      exact hh.2


theorem phase_disk_normal_gluing (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (hn : ContMDiff planeModel spaceModel ∞ n)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D)
    {U₀ : Set SmallModes.Base} (hU₀ : IsOpen U₀) {ν : SmallModes.Base → Vec}
    (hν : ContDiffOn ℝ ∞ ν U₀) (hunit : ∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1)
    (hnormal : ∀ x ∈ U₀, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ ν x = 0)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (hproj : ∀ p ∉ D, A.projectedNormalField F n p ≠ 0)
    (hanti : ∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField F n p) ≠
      -ν (baseEquiv (e (chart (i : M) p))))
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, Continuous (B k))
    (hin : ∀ k p, p ∈ C k → p ∈ D →
      ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize (B k p))
    (hout : ∀ k p, p ∈ C k → p ∉ closure D →
      spaceCoordinates (A.unitProjectedNormalField F n p) ≠ -normalize (B k p))
    (hpair : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < B k p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
      0 < B k p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField F n p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ ∃ N : PreferredNormal F,
      (∀ p ∈ D \ W, N.vector p = A.phaseNormalLift i e ν p) ∧
      (∀ p ∈ (closure D)ᶜ \ W, N.vector p = A.unitProjectedNormalField F n p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨W,hW,hfW,_,N,hNa,hNb,havoid⟩ := A.phase_disk_normal_gluing_within i
    hF hI hn houter e he hi univ isOpen_univ hD (subset_univ _) hU₀ hν hunit hnormal
    hDs hDe hDU hDw hproj hanti C hC B hB hin hout hpair
  exact ⟨W,hW,hfW,N,hNa,hNb,havoid⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
