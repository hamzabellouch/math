import OAI.Geometry.RCD.Transport.PointedGeodesicWithin
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! # Midpoints of arbitrary compact target sets -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

/-- The exact midpoint image, without a convexity assumption. -/
def midpointSet {n : ℕ} (A B : Set (Euclidean n)) : Set (Euclidean n) :=
  (fun z : Euclidean n × Euclidean n => (1/2:ℝ) • (z.1+z.2)) '' (A ×ˢ B)

theorem isCompact_midpointSet {n : ℕ} {A B : Set (Euclidean n)}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (midpointSet A B) :=
  (hA.prod hB).image (by fun_prop)

theorem pointed_midpoint_sets_within {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r S ρ ε : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) (he : 0 ≤ ε)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    {A B : Set (Euclidean n)} {γ : C(Time,X)} (hγ : IsGeodesic γ)
    (h0 : dist (γ 0) p ≤ ρ*r) (h1 : dist (γ 1) p ≤ ρ*r)
    (hpoints : ∀ t : Time, dist (γ t) p ≤ S*r)
    (hA : V (γ 0) ∈ A) (hB : V (γ 1) ∈ B) :
    V (γ midpointTime) ∈ cthickening (Real.sqrt (2*(ε*(4*ρ+ε)))) (midpointSet A B) := by
  have hh := pointed_geodesic_interpolation_within hr hρ he hV hγ h0 h1 hpoints midpointTime
  have hmid : (1/2:ℝ) • (V (γ 0)+V (γ 1)) ∈ midpointSet A B :=
    ⟨(V (γ 0),V (γ 1)),⟨hA,hB⟩,rfl⟩
  apply mem_cthickening_of_dist_le _ _ _ _ hmid
  simpa only [midpointTime,show (1-(1/2:ℝ))=1/2 by norm_num,smul_add] using hh

end RegularPointCoordinates

end

end OAI
