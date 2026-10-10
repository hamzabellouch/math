import OAI.Geometry.SurfaceImmersion.Atlas.PhaseDiskNormalGluing
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

theorem crossing_safe_phase_normal_gluing (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (hn : ContMDiff planeModel spaceModel ∞ n)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D)
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D))
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
    ∃ N : PreferredNormal F,
      (∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p)) ∧
      ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
        (p ∉ D → N.vector p = A.unitProjectedNormalField F n p) := by
  have hf : frontier D ⊆ Eᶜ := fun p hp he => Set.disjoint_left.mp hEf he hp
  obtain ⟨W,hW,_,hWE,N,hNa,hNb,havoid⟩ := A.phase_disk_normal_gluing_within i hF hI
    hn houter e he hi Eᶜ hE.isClosed.isOpen_compl hD hf hU₀ hν hunit hnormal
    hDs hDe hDU hDw hproj hanti C hC B hB hin hout hpair
  refine ⟨N,havoid,?_⟩
  intro p hp
  have hpW : p ∉ W := fun hw => hWE hw hp
  refine ⟨fun hpD => hNa p ⟨hpD,hpW⟩,?_⟩
  intro hpD
  have hpc : p ∉ closure D := by
    intro hpc
    have hpf : p ∈ frontier D := by rw [hD.frontier_eq]; exact ⟨hpc,hpD⟩
    exact Set.disjoint_left.mp hEf hp hpf
  exact hNb p ⟨hpc,hpW⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
