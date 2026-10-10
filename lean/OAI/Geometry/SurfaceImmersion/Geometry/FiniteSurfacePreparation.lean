import OAI.Geometry.SurfaceImmersion.Correction.FiniteSurfaceCorrectionBounds
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionApproximation

namespace OAI

/-! Finite prescribed points can be prepared by one globally defined small
correction, with its C2 constant fixed before the finite set is supplied. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_spherical_preparation_correction {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (c : P → A.centers) (Q : M → Space),
        (∀ p, A.weight (c p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ Q ∧
        A.WeightedBound 1 1 ε Q ∧ A.WeightedBound 1 2 D Q ∧
        let G := radialNormalize ∘ (F+Q)
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
            (chartAt Plane (c p : M) p) v w = 0 := by
  classical
  obtain ⟨D,hD,hbudget⟩ := A.finite_surface_correction_budgets hF hunit
  refine ⟨D,hD,?_⟩
  intro P ε hε
  choose c hc using fun p : P => A.mem_some_weightCore (p : M)
  have hcn (p : P) : A.weight (c p) p ≠ 0 := A.weightCore_nonzero (c p) (hc p)
  let U (p : P) : Set M := {x | A.weight (c p) x ≠ 0}
  have hU (p : P) : IsOpen (U p) := isOpen_ne_fun (A.weight_smooth (c p)).continuous continuous_const
  have hpU (p : P) : (p : M) ∈ U p := hcn p
  let η := min 1 (ε/(D+1))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hDη : D*η ≤ ε := by
    have hm := min_le_right (1 : ℝ) (ε/(D+1))
    have hh : (D+1)*η ≤ ε := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < D+1)).mp hm
    nlinarith
  obtain ⟨r,hr,hdisj⟩ := finite_point_chart_balls P
    (fun p => chartAt Plane (c p : M))
    (fun p => by simpa only [chart_source] using (A.weight_support (c p) (subset_tsupport _ (hcn p))))
    U hU hpU hη
  have ht (p : P) : closedBall (chartAt Plane (c p : M) p) (r p) ⊆
      (chartAt Plane (c p : M)).target := fun _ hx => (hr p).2.2 hx |>.1
  obtain ⟨hb1,hb2⟩ := hbudget P c r η hη hη1 hcn
    (fun p => ⟨(hr p).1,(hr p).2.1.le⟩) ht hdisj
  refine ⟨c,A.finiteSurfaceQuadratic P c r F,hcn,
    A.finiteSurfaceQuadratic_smooth P c r F,?_,hb2,?_⟩
  · exact fun i => (hb1 i).mono_const hDη
  · exact A.finiteSurfaceQuadratic_flattening P c r F hF hunit hcn
      (fun p => (hr p).1) ht hdisj

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
