import OAI.Geometry.SurfaceImmersion.Geometry.UniformSmallStartingMetric

namespace OAI

/-! A spherical family with a uniformly small induced metric, with the
scale chosen before the finite set at which the spherical second form vanishes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

theorem small_metric_starting_family (g : SmoothMetric M)
    (hW : PublishedInputs.WhitneySurfaceInput M) {η : ℝ} (hη : 0 < η) :
    ∃ (I : M → Space) (A : SmoothingAtlas M) (r D c : ℝ),
      ContMDiff planeModel spaceModel ∞ I ∧ (∀ p, ‖I p‖ = 1) ∧
      0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (a : P → A.centers) (G : M → Space) (n : PreferredNormal (r • G)),
        (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p)) ∧
        n.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        A.TensorWeightedBound 1 1 η (inducedTensor (r • G)) ∧
        (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        ∀ p : P, G p = I p ∧
          fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
            fderiv ℝ (I ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
            (chartAt Plane (a p : M) p) v w = 0 := by
  obtain ⟨I,hI,hunit,hImm,⟨data⟩⟩ := metricPhaseData_of_whitney g hW
  let A := data.A
  obtain ⟨D,c,hD,hc,hprep⟩ := A.uniform_prepared_spherical_immersion g hI hunit hImm
  obtain ⟨r,hr,hr1,hsmall⟩ := A.uniform_small_scaled_metric g hD hη
  refine ⟨I,A,r,D,c,hI,hunit,hr,hr1,hD,hc,?_⟩
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
    (hsmall G hG hbound).1,(hsmall G hG hbound).2,hflat⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
