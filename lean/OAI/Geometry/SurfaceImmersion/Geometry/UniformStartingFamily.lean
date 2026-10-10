import OAI.Geometry.SurfaceImmersion.Geometry.UniformPreparedSphericalImmersion
import OAI.Geometry.SurfaceImmersion.Geometry.UniformInitialScale
import OAI.Geometry.SurfaceImmersion.Whitney.WhitneyStartingGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormal

namespace OAI

/-! The starting family for the global preparation, conditional only on
Whitney's published compact-surface immersion theorem. All uniform constants
are fixed before the boundary intersections are specified. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def PreferredNormal.const_smul {F : M → Space} (n : PreferredNormal F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ) : PreferredNormal (r • F) where
  vector := n.vector
  smooth := n.smooth
  unit := n.unit
  normal p v := by
    have hd := const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) r
    change inner ℝ (show Space from mfderiv planeModel spaceModel (r • F) p v) (n.vector p) = 0
    rw [hd]
    change inner ℝ (r • (show Space from mfderiv planeModel spaceModel F p v)) (n.vector p) = 0
    rw [real_inner_smul_left,n.normal,mul_zero]

namespace FiniteOrderSmoothing
open SphericalJets
variable [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

theorem uniform_starting_family (g : SmoothMetric M)
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ (I : M → Space) (A : SmoothingAtlas M) (r D c : ℝ),
      ContMDiff planeModel spaceModel ∞ I ∧ (∀ p, ‖I p‖ = 1) ∧
      0 < r ∧ 0 ≤ D ∧ 0 < c ∧
      ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (a : P → A.centers) (G : M → Space) (n : PreferredNormal (r • G)),
        (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p)) ∧
        n.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        ∀ p : P, G p = I p ∧
          fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
            fderiv ℝ (I ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
            (chartAt Plane (a p : M) p) v w = 0 := by
  obtain ⟨I,hI,hunit,hImm,⟨data⟩⟩ := metricPhaseData_of_whitney g hW
  let A := data.A
  obtain ⟨D,c,hD,hc,hprep⟩ := A.uniform_prepared_spherical_immersion g hI hunit hImm
  obtain ⟨r,hr,hshort⟩ := A.uniform_initial_short_scale g hD
  refine ⟨I,A,r,D,c,hI,hunit,hr,hD,hc,?_⟩
  intro P ε hε
  obtain ⟨a,G,ha,hG,hu,hGI,hclose,hbound,hlower,hflat⟩ := hprep P ε hε
  let n := (sphericalPreferredNormal hG hu).const_smul hG r
  have hscaled : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p) := by
    intro p v w h
    have hd := const_smul_mfderiv ((hG p).mdifferentiableAt (by simp)) r
    have he := congrArg (fun z : Space => r⁻¹ • z) h
    rw [hd] at he
    change r⁻¹ • (r • (mfderiv planeModel spaceModel G p v)) =
      r⁻¹ • (r • (mfderiv planeModel spaceModel G p w)) at he
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] at he
    exact hGI p he
  exact ⟨a,G,n,ha,hG,hu,hscaled,rfl,hclose,hbound,hlower,
    hshort G hG (fun i => (hbound i).mono_order (by omega)),hflat⟩

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
