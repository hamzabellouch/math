import OAI.Geometry.SurfaceImmersion.Geometry.IndependentPrefixBounds
import OAI.Geometry.SurfaceImmersion.Primitive.UniformConvexCircularAtlas
import OAI.Geometry.SurfaceImmersion.Primitive.CircularDiskTopology

namespace OAI

/-! Apply the finite geometric iteration using independently chosen local
convex phases and one fixed background norm for all prefix bounds. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

omit [CompactSpace M] in
lemma circular_weight_support {B : SmoothingAtlas M} (r : B.centers → ℝ)
    (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
    (hnon : ∀ i p, 0 ≤ B.weight i p)
    (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
    (i : B.centers) : tsupport (B.weight i) ⊆ circularDiskClosure (i : M) (r i) := by
  apply closure_minimal _ (circularDiskClosure_compact (i : M) (r i) (hreg i)).isClosed
  intro p hp
  have hd := (hpos i p).mp (lt_of_le_of_ne (hnon i p) (Ne.symm hp))
  exact (circularDiskClosure_iff (i : M) (hreg i) p).mpr ⟨hd.1,hd.2.le⟩

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem independent_circular_realization (g : SmoothMetric M) (c C : ℝ)
    (B : SmoothingAtlas M) (r L K : B.centers → ℝ)
    (hL : ∀ i, 0 < L i)
    (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
    (hnon : ∀ i p, 0 ≤ B.weight i p)
    (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
    (hphase : ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 (C+1) h.inner →
      (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
      ∀ (i : B.centers) (q : M), q ∈ circularDiskClosure (i : M) (r i) →
        ∀ ell : Base, ‖ell‖ ≤ K i → ∀ v : Base,
          (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
            (centeredConvexPhase ell (L i) (coordinateChart (i : M) i))
            (coordinateChart (i : M) q) v v)
    (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N : ℕ, 0 < N ∧ ∀ g₀ : SmoothMetric M,
      (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
      ∀ (u : ∀ p : M, CovariantTwoTensor p)
        (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
      (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
      (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
      ∀ d : CircularPrimitiveFamily B (Fin (N*m)),
      (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
      (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
      (∀ a, d.convexPart a = L (d.curves a).index) →
      (∀ a, ‖d.linearPart a‖ ≤ K (d.curves a).index) →
      ∀ h : SmoothMetric M, h.inner = g₀.inner+u →
      ∀ (F : M → Space) (n : PreferredNormal F), IsSmoothIsometricImmersion M g₀ F →
        MetricGoodPhaseData g₀ F →
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
      ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  obtain ⟨N,hN,hbounds⟩ := A.independent_prefix_bounds m D hD
  refine ⟨N,hN,?_⟩
  intro g₀ hlower u f hb hpath d ha hp hpart hell h htarget F n hF data hgeom
  have hcv (a : Fin (N*m)) : d.ConvexMetric (d.prefixMetric g₀ a.castSucc) a := by
    intro q hq _hqrad v hv
    obtain ⟨hbound,hlow⟩ := hbounds B g g₀ c C hlower u f hb hpath d ha hp a
    have hqc := circular_weight_support r hreg hnon hpos (d.curves a).index hq
    have he := hphase _ hbound hlow (d.curves a).index q hqc (d.linearPart a) (hell a) v
    rw [hpart]
    have hs : 0 < v.1^2+v.2^2 := by
      by_contra hn
      have h1 : v.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg v.2])
      have h2 : v.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg v.1])
      exact hv (Prod.ext h1 h2)
    exact (mul_pos (half_pos (hL _)) hs).trans_le he
  apply d.realize_total g₀ h _ hcv n hF data hgeom
  rw [d.totalTensor_cycle f ha hp hN]
  exact htarget

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
