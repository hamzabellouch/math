import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryRemovalStep

namespace OAI

/-! The concrete finite circular data used in the global primitive iteration.
All geometric fields are furnished by the generic radius/phase preparation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

structure CircularPrimitiveFamily (B : SmoothingAtlas M) (ι : Type*) [Fintype ι] where
  curves : ι → PhaseBoundaryCurve B
  radius : ι → ℝ
  outerRadius : ι → ℝ
  chartRadius : ι → ℝ
  linearPart : ι → Base
  convexPart : ι → ℝ
  radius_pos : ∀ a, 0 < radius a
  radius_outer : ∀ a, (radius a)^2 < (outerRadius a)^2
  radius_chart : ∀ a, radius a < chartRadius a
  weight_positive : ∀ a p, 0 < B.weight (curves a).index p ↔
    p ∈ circularCoordinateDisk ((curves a).index : M) (outerRadius a)
  region : ∀ a, circularCoordinateRegion ((curves a).index : M) (radius a) ⊆
    (coordinateChart ((curves a).index : M)).target
  carrier : ∀ a, (curves a).carrier = circularBoundary ((curves a).index : M) (radius a)
  cover : ∀ a x, x ∈ circularCoordinateRegion ((curves a).index : M) (radius a) →
    baseEquiv.symm x ∈ (curves a).phase.source
  first_coordinate : ∀ a x, (baseEquiv ((curves a).phase x)).1 =
    centeredConvexPhase (linearPart a) (convexPart a)
      (coordinateChart ((curves a).index : M) (curves a).index) (baseEquiv x)
  pair_finite : ∀ a b, a ≠ b → ((curves a).carrier ∩ (curves b).carrier).Finite
  triple_empty : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    (curves a).carrier ∩ (curves b).carrier ∩ (curves c).carrier = ∅
  tangencies_finite : ∀ a b, (circularPhaseTangencies ((curves a).index : M) ((curves b).index : M)
    (linearPart a) (convexPart a) (radius b) (radius a)).Finite
  independent : ∀ a b, a ≠ b → ∀ p ∈ boundaryCrossingSet curves univ,
    p ∈ (coordinateChart ((curves a).index : M)).source →
    p ∈ (coordinateChart ((curves b).index : M)).source →
    covectorDet
      (phaseDerivative (centeredAtlasPhase ((curves a).index : M) (linearPart a) (convexPart a) ∘
        (coordinateChart ((curves a).index : M)).symm) (coordinateChart ((curves a).index : M) p))
      (phaseDerivative (centeredAtlasPhase ((curves b).index : M) (linearPart b) (convexPart b) ∘
        (coordinateChart ((curves a).index : M)).symm) (coordinateChart ((curves a).index : M) p)) ≠ 0
  amplitude : ι → M → ℝ
  phase : ι → M → ℝ
  phase_smooth : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phase a)
  amplitude_smooth : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amplitude a)
  amplitude_nonneg : ∀ a p, 0 ≤ amplitude a p
  amplitude_positive : ∀ a p, 0 < amplitude a p ↔
    p ∈ circularCoordinateDisk ((curves a).index : M) (radius a)
  phase_germ : ∀ a p, p ∈ circularCoordinateDisk ((curves a).index : M) (radius a) →
    phase a =ᶠ[𝓝 p] (fun q => ((curves a).phase (chart ((curves a).index : M) q)) 0)

namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

 def restrict (d : CircularPrimitiveFamily B ι) {κ : Type*} [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) : CircularPrimitiveFamily B κ where
  curves := d.curves ∘ f
  radius := d.radius ∘ f
  outerRadius := d.outerRadius ∘ f
  chartRadius := d.chartRadius ∘ f
  linearPart := d.linearPart ∘ f
  convexPart := d.convexPart ∘ f
  radius_pos a := d.radius_pos (f a)
  radius_outer a := d.radius_outer (f a)
  radius_chart a := d.radius_chart (f a)
  weight_positive a := d.weight_positive (f a)
  region a := d.region (f a)
  carrier a := d.carrier (f a)
  cover a := d.cover (f a)
  first_coordinate a := d.first_coordinate (f a)
  pair_finite a b hab := d.pair_finite (f a) (f b) (fun h => hab (hf h))
  triple_empty a b c hab hac hbc := d.triple_empty (f a) (f b) (f c)
    (fun h => hab (hf h)) (fun h => hac (hf h)) (fun h => hbc (hf h))
  tangencies_finite a b := d.tangencies_finite (f a) (f b)
  independent a b hab p hp hpa hpb := by
    apply d.independent (f a) (f b) (fun h => hab (hf h)) p _ hpa hpb
    obtain ⟨j,_,k,_,hjk,hj,hk⟩ := hp
    exact ⟨f j,mem_univ _,f k,mem_univ _,fun h => hjk (hf h),hj,hk⟩
  amplitude := d.amplitude ∘ f
  phase := d.phase ∘ f
  phase_smooth a := d.phase_smooth (f a)
  amplitude_smooth a := d.amplitude_smooth (f a)
  amplitude_nonneg a := d.amplitude_nonneg (f a)
  amplitude_positive a := d.amplitude_positive (f a)
  phase_germ a := d.phase_germ (f a)

 theorem one_step [DecidableEq ι] (d : CircularPrimitiveFamily B ι) (a : ι)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F) (hgeom : FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n)
    (hconvex : ∀ p ∈ tsupport (B.weight (d.curves a).index),
      ‖coordinateChart ((d.curves a).index : M) p-coordinateChart ((d.curves a).index : M) (d.curves a).index‖ ≤ d.chartRadius a →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((d.curves a).index : M))
        (centeredConvexPhase (d.linearPart a) (d.convexPart a)
          (coordinateChart ((d.curves a).index : M) (d.curves a).index))
        (coordinateChart ((d.curves a).index : M) p) v v)
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => d.curves j)
          (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => d.curves j) univ) W N := by
  apply circular_boundary_removal_step d.curves a d.radius d.outerRadius d.chartRadius
    d.radius_pos (d.radius_outer a) (d.radius_chart a) (d.weight_positive a) d.region d.carrier d.cover
    d.linearPart d.convexPart d.first_coordinate d.pair_finite d.triple_empty
    (d.tangencies_finite a) ?_ hF n hgeom hconvex (d.amplitude_smooth a)
    (d.amplitude_nonneg a) (d.amplitude_positive a) (d.phase_germ a) data h htarget
  intro j k hjk p hp hj hk
  apply d.independent j k hjk p _ hj hk
  rwa [boundaryCrossingSet_eq_circular d.curves d.radius d.carrier]

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
