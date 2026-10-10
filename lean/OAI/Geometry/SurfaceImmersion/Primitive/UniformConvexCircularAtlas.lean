import OAI.Geometry.SurfaceImmersion.Geometry.LocalUniformConvexity

namespace OAI

/-! A circular cover selected after local phase convexity has been fixed.
All metric bounds are measured in the original, independent atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

omit [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] in
lemma circular_radius_le_of_subordinate (p : M) {r R : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (hsmall : ∀ q ∈ circularDiskClosure p r,
      ‖coordinateChart p q-coordinateChart p p‖ < R) : r ≤ R := by
  let x : Base := ((coordinateChart p p).1+r,(coordinateChart p p).2)
  have hx : x ∈ circularCoordinateRegion p r := by
    change circularRadiusSquared (coordinateChart p p) x ≤ r^2
    dsimp [x,circularRadiusSquared]
    ring_nf
    exact le_refl _
  have hh := hsmall ((coordinateChart p).symm x) ⟨x,hx,rfl⟩
  rw [(coordinateChart p).right_inv (hreg hx)] at hh
  have he : x-coordinateChart p p = (r,0) := by ext <;> simp [x]
  rw [he,Prod.norm_def] at hh
  simpa only [Real.norm_eq_abs,abs_of_pos hr,norm_zero,max_eq_left hr.le] using hh.le

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_convex_circular_atlas (g : SmoothMetric M) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (K : M → ℝ) (hK : ∀ p, 0 ≤ K p) :
    ∃ L : M → ℝ, (∀ p, 0 < L p) ∧
      ∀ R : M → ℝ, (∀ p, 0 < R p) →
      ∀ V : M → Set M, (∀ p, IsOpen (V p)) → (∀ p, p ∈ V p) →
      ∃ (B : SmoothingAtlas M) (r : B.centers → ℝ),
        (∀ i : B.centers, 0 < r i ∧ r i ≤ R (i : M)) ∧
        (∀ i : B.centers, circularDiskClosure (i : M) (r i) ⊆ V i) ∧
        (∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target) ∧
        (∀ i p, 0 ≤ B.weight i p) ∧
        (∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i)) ∧
        (∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1)) ∧
        ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
          (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
          ∀ (i : B.centers) (q : M), q ∈ circularDiskClosure (i : M) (r i) →
            ∀ ell : Base, ‖ell‖ ≤ K i → ∀ v : Base,
              (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
                (centeredConvexPhase ell (L i) (coordinateChart (i : M) (i : M)))
                (coordinateChart (i : M) q) v v := by
  classical
  choose L U hL hU hpU hUs hconvex using fun p =>
    A.local_uniform_convexity g hc hC (hK p) p
  refine ⟨L,hL,?_⟩
  intro R hR V hV hpV
  let W : M → Set M := fun p => (U p ∩ V p) ∩ ((coordinateChart p).source ∩
    (coordinateChart p) ⁻¹' Metric.ball (coordinateChart p p) (R p))
  have hW (p : M) : IsOpen (W p) :=
    ((hU p).inter (hV p)).inter ((coordinateChart p).isOpen_inter_preimage Metric.isOpen_ball)
  have hpW (p : M) : p ∈ W p := by
    refine ⟨⟨hpU p,hpV p⟩,?_,Metric.mem_ball_self (hR p)⟩
    rw [coordinateChart_source]; exact mem_chart_source Plane p
  obtain ⟨B,r,hr,hreg,hinside,hwnon,hwpos,_hsupp,houter⟩ :=
    exists_circular_smoothingAtlas W hW hpW
  refine ⟨B,r,fun i => ⟨hr i,?_⟩,(fun i p hp => (hinside i hp).1.2),hreg,hwnon,hwpos,houter,?_⟩
  · apply circular_radius_le_of_subordinate (i : M) (hr i) (hreg i)
    intro q hq
    have hh : coordinateChart (i : M) q ∈ Metric.ball (coordinateChart (i : M) (i : M)) (R (i : M)) :=
      (hinside i hq).2.2
    simpa only [Metric.mem_ball,dist_eq_norm] using hh
  · intro h hb hlower i q hq ell hell v
    exact hconvex i h hb hlower q (hinside i hq).1.1 ell hell v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
