import OAI.Geometry.SurfaceImmersion.Atlas.FixedAtlasStartingFamily

namespace OAI

/-! Uniform finite-point spherical preparation on a prescribed atlas.
The same atlas can therefore be used for the circular boundary preparation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem reference_small_metric_prepared_family (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ,
      0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      A.WeightedBound 1 2 D I ∧
      A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
      (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
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
  obtain ⟨D,c,hD,hc,hprep⟩ := A.uniform_prepared_spherical_immersion g hI hunit hImm
  obtain ⟨D₀,hD₀,hIbound⟩ := A.exists_weighted_bound 2 hI
  let E := D+D₀
  have hE : 0 ≤ E := add_nonneg hD hD₀
  have hIb : A.WeightedBound 1 2 E I := fun i => (hIbound i).mono_const (by dsimp [E]; linarith)
  obtain ⟨r,hr,hr1,hsmall⟩ := A.uniform_small_scaled_metric g hE hη
  have href := hsmall I hI hIb
  refine ⟨r,E,c,hr,hr1,hE,hc,hIb,href.1,href.2,?_⟩
  intro P ε hε
  obtain ⟨a,G,ha,hG,hu,hGI,hclose,hbound,hlower,hflat⟩ := hprep P ε hε
  have hGb : A.WeightedBound 1 2 E G := fun i => (hbound i).mono_const (by dsimp [E]; linarith)
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
  exact ⟨a,G,n,ha,hG,hu,hscaled,rfl,hclose,hGb,hlower,
    (hsmall G hG hGb).1,(hsmall G hG hGb).2,hflat⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
