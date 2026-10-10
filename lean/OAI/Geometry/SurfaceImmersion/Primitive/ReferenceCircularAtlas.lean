import OAI.Geometry.SurfaceImmersion.Primitive.UniformConvexCircularAtlas
import OAI.Geometry.SurfaceImmersion.Atlas.LocalReferencePhaseBasis
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseParameterBalls

namespace OAI

/-! A reference circular atlas with positive coefficient forms and convex
phases, chosen before the number of cycles or generic perturbations. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

structure ReferenceCircularAtlas (A : SmoothingAtlas M) (gref g : SmoothMetric M) (c C : ℝ) where
  B : SmoothingAtlas M
  P : B.centers → PhaseBasis
  L : B.centers → ℝ
  radius : B.centers → ℝ
  epsilon : B.centers → ℝ
  L_pos : ∀ i, 0 < L i
  radius_pos : ∀ i, 0 < radius i
  epsilon_pos : ∀ i, 0 < epsilon i
  region : ∀ i : B.centers, circularCoordinateRegion (i : M) (radius i) ⊆ (coordinateChart (i : M)).target
  weight_nonneg : ∀ i p, 0 ≤ B.weight i p
  weight_positive : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (radius i)
  outer : ∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1)
  parameters : ∀ i j ell, ell ∈ Metric.closedBall ((P i).ξ j) (epsilon i) →
    ell ≠ 0 ∧ ‖ell‖ ≤ ‖(P i).ξ‖+1
  admissible : ∀ (i : B.centers) p, p ∈ circularDiskClosure (i : M) (radius i) →
    admissiblePhaseCovectors (P i) (fun j => phaseDerivative
      (centeredConvexPhase ((P i).ξ j) (L i) (coordinateChart (i : M) i)) (coordinateChart (i : M) p))
  positive : ∀ (i : B.centers) p, p ∈ circularDiskClosure (i : M) (radius i) → ∀ j,
    0 < (centeredSpatialBasis (P i) (P i).ξ (L i) (coordinateChart (i : M) i)
      (coordinateChart (i : M) p)).Q j (coordinateMetric gref (i : M) (coordinateChart (i : M) p))
  convex : ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
    (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
    ∀ (i : B.centers) p, p ∈ circularDiskClosure (i : M) (radius i) →
      ∀ ell : Base, ‖ell‖ ≤ ‖(P i).ξ‖+1 → ∀ v : Base,
        (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
          (centeredConvexPhase ell (L i) (coordinateChart (i : M) i)) (coordinateChart (i : M) p) v v
  charts : ∀ (i : B.centers) j ell, ell ∈ Metric.closedBall ((P i).ξ j) (epsilon i) →
    ∃ e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base,
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ x, (baseEquiv (e x)).1 = centeredConvexPhase ell (L i)
        (coordinateChart (i : M) i) (baseEquiv x)) ∧
      ∀ x ∈ circularCoordinateRegion (i : M) (radius i), baseEquiv.symm x ∈ e.source

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_reference_circular_atlas (gref g : SmoothMetric M) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) : Nonempty (ReferenceCircularAtlas A gref g c C) := by
  classical
  choose P hP using fun p : M => positive_tensor_has_basis
    (coordinateMetric_positive_center gref p).1 (coordinateMetric_positive_center gref p).2
  choose eps heps heps1 hparams using fun p => phase_parameter_balls (P p)
  obtain ⟨L,hL,hchoose⟩ := A.uniform_convex_circular_atlas g hc hC
    (fun p => ‖(P p).ξ‖+1) (fun _ => by positivity)
  choose R hR hcharts using fun (p : M) (j : Fin 3) =>
    uniform_circular_phase_charts (M := M) (isCompact_closedBall ((P p).ξ j) (eps p))
      (fun ell hell => ((hparams p j).2 ell hell).1) (hL p)
  let R₀ : M → ℝ := fun p => min (R p 0) (min (R p 1) (R p 2))
  have hR₀ (p : M) : 0 < R₀ p := lt_min (hR p 0) (lt_min (hR p 1) (hR p 2))
  have hRle (p : M) (j : Fin 3) : R₀ p ≤ R p j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  choose U hU hpU hUs hgood using fun p => local_reference_phase_basis gref p (P p) (hP p) (L p)
  obtain ⟨B,r,hr,hinside,hreg,hnon,hpos,houter,hconvex⟩ := hchoose R₀ hR₀ U hU hpU
  refine ⟨{
    B := B, P := fun i => P i, L := fun i => L i,
    radius := r, epsilon := fun i => eps i,
    L_pos := fun i => hL i, radius_pos := fun i => (hr i).1,
    epsilon_pos := fun i => heps i, region := hreg,
    weight_nonneg := hnon, weight_positive := hpos, outer := houter,
    parameters := fun i j ell hell => (hparams i j).2 ell hell,
    admissible := fun i p hp => (hgood i p (hinside i hp)).1,
    positive := fun i p hp => (hgood i p (hinside i hp)).2,
    convex := hconvex,
    charts := ?_ }⟩
  intro i j ell hell
  obtain ⟨e,he,hei,heq,hcover⟩ := hcharts (i : M) j (i : M) ell hell
  exact ⟨e,he,hei,heq,hcover (r i) (hr i).1.le ((hr i).2.trans (hRle i j))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
