import OAI.Geometry.Immersion.ClosedSurface.PhasePatches
import OAI.Geometry.Immersion.ClosedSurface.MetricPullback

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]




theorem finite_metric_phase_patches (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) :
    ∃ (P : ∀ p, PhasePatch F (coordinateMetric g p) p)
        (t : Finset M) (ψ : t → M → ℝ),
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ (P i).V) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  exact exists_finite_phase_patches hF hImm hB (coordinateMetric g)
    (coordinateMetric_continuousAt_center g)
    (fun p => (coordinateMetric_positive_center g p).1)
    (fun p => (coordinateMetric_positive_center g p).2)

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

def chartCoordinates (p : M) : M → Base := planeCoordinates ∘ chartAt Plane p

def chartSupport (p : M) (ψ : M → ℝ) : Set Base := chartCoordinates p '' tsupport ψ

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma chartCoordinates_continuousOn (p : M) :
    ContinuousOn (chartCoordinates p) (chartAt Plane p).source :=
  planeCoordinates.continuous.comp_continuousOn (chartAt Plane p).continuousOn

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma chartCoordinates_center (p : M) : chartCoordinates p p = coordinateCenter p := by
  simp [chartCoordinates,coordinateCenter,planeModel]




theorem exists_fixed_convex_coordinate_cover :
    ∃ (t : Finset M) (r : t → ℝ) (ψ : t → M → ℝ),
      (∀ i : t, 0 < r i) ∧
      (∀ i : t, Metric.closedBall (coordinateCenter (i : M)) (r i) ⊆ coordinateDomain (i : M)) ∧
      (∀ i : t, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i : t, HasCompactSupport (ψ i)) ∧
      (∀ i : t, tsupport (ψ i) ⊆ (chartAt Plane (i : M)).source) ∧
      (∀ i : t, IsCompact (chartSupport (i : M) (ψ i))) ∧
      (∀ i : t, chartSupport (i : M) (ψ i) ⊆ Metric.ball (coordinateCenter (i : M)) (r i/2)) ∧
      (∀ (i : t) p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  have hrad (p : M) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (coordinateCenter p) r ⊆ coordinateDomain p := by
    obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp (coordinateDomain_open p)
      (coordinateCenter p) (coordinateCenter_mem p)
    refine ⟨R/2,half_pos hR,fun x hx => hball ?_⟩
    exact lt_of_le_of_lt hx (half_lt_self hR)
  choose r hr hdomain using hrad
  let V (p : M) : Set M := (chartAt Plane p).source ∩
    chartCoordinates p ⁻¹' Metric.ball (coordinateCenter p) (r p/2)
  have hV (p : M) : IsOpen (V p) :=
    (chartAt Plane p).isOpen_inter_preimage
      (Metric.isOpen_ball.preimage planeCoordinates.continuous)
  have hpV (p : M) : p ∈ V p := by
    refine ⟨mem_chart_source Plane p,?_⟩
    change dist (chartCoordinates p p) (coordinateCenter p) < r p/2
    rw [chartCoordinates_center,dist_self]
    exact half_pos (hr p)
  obtain ⟨t,ψ,hsmooth,hsupport,hcompact,hnonneg,hsquares⟩ :=
    exists_finite_smooth_square_partition (E := Plane) V hV hpV
  refine ⟨t,fun i => r i,ψ,fun i => hr i,fun i => hdomain i,hsmooth,hcompact,?_,?_,?_,hnonneg,hsquares⟩
  · exact fun i x hx => (hsupport i hx).1
  · intro i
    exact (hcompact i).image_of_continuousOn ((chartCoordinates_continuousOn (i : M)).mono
      (fun x hx => (hsupport i hx).1))
  · intro i x hx
    obtain ⟨q,hq,rfl⟩ := hx
    exact (hsupport i hq).2

end ClosedSurfaceR4

end

end OAI
