import OAI.Geometry.SurfaceImmersion.Primitive.CircularPrimitiveFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PreparedCircularPhaseCurves

namespace OAI

/-! The finite generic boundary geometry is chosen before any amplitudes
or finite-point spherical modification. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

structure CircularFamilyGeometry (B : SmoothingAtlas M) (ι : Type*) [Fintype ι] where
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

namespace CircularFamilyGeometry
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

def withAmplitudes (d : CircularFamilyGeometry B ι) (amp phi : ι → M → ℝ)
    (hamp : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amp a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hamp0 : ∀ a p, 0 ≤ amp a p)
    (hpos : ∀ a p, 0 < amp a p ↔ p ∈ circularCoordinateDisk ((d.curves a).index : M) (d.radius a))
    (hgerm : ∀ a p, p ∈ circularCoordinateDisk ((d.curves a).index : M) (d.radius a) →
      phi a =ᶠ[𝓝 p] (fun q => ((d.curves a).phase (chart ((d.curves a).index : M) q)) 0)) :
    CircularPrimitiveFamily B ι where
  curves := d.curves
  radius := d.radius
  outerRadius := d.outerRadius
  chartRadius := d.chartRadius
  linearPart := d.linearPart
  convexPart := d.convexPart
  radius_pos := d.radius_pos
  radius_outer := d.radius_outer
  radius_chart := d.radius_chart
  weight_positive := d.weight_positive
  region := d.region
  carrier := d.carrier
  cover := d.cover
  first_coordinate := d.first_coordinate
  pair_finite := d.pair_finite
  triple_empty := d.triple_empty
  tangencies_finite := d.tangencies_finite
  independent := d.independent
  amplitude := amp
  phase := phi
  phase_smooth := hphi
  amplitude_smooth := hamp
  amplitude_nonneg := hamp0
  amplitude_positive := hpos
  phase_germ := hgerm

end CircularFamilyGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
