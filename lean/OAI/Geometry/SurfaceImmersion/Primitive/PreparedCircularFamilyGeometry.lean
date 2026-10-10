import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyGeometry

namespace OAI

/-! Selection of the whole finite circular geometry, before amplitudes are known. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

 theorem prepared_circular_family_geometry (P : ι → Set Base)
    (hP : ∀ i, IsCompact (P i)) (hP0 : ∀ i ell, ell ∈ P i → ell ≠ 0)
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ R : ι → ℝ, (∀ i, 0 < R i) ∧
      ∀ (index : ι → A.centers) (r₀ lo hi : ι → ℝ),
      (∀ i, 0 < lo i) → (∀ i, lo i < hi i) → (∀ i, hi i < r₀ i) →
      (∀ i, r₀ i ≤ R i) →
      (∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r₀ i)) →
      (∀ i, circularCoordinateRegion (index i : M) (r₀ i) ⊆ (coordinateChart (index i : M)).target) →
      ∀ U : Set (ι → Base), IsOpen U → U.Nonempty → (∀ ell ∈ U, ∀ i, ell i ∈ P i) →
      ∃ d : CircularFamilyGeometry A ι,
        d.linearPart ∈ U ∧ (∀ i, lo i < d.radius i ∧ d.radius i < hi i) ∧
        (∀ i, (d.curves i).index = index i) ∧
        d.outerRadius = r₀ ∧ d.chartRadius = r₀ ∧ d.convexPart = L := by
  obtain ⟨R,hR,hchoose⟩ := A.prepared_circular_phase_curves P hP hP0 L hL
  refine ⟨R,hR,?_⟩
  intro index r₀ lo hi hlo hlohi hhi hrR hpos hreg U hU hne hUP
  obtain ⟨r,ell,curves,hell,hr,hindex,hcarrier,hphase,hcover,hcross,htriple,htrans,htan,hind⟩ :=
    hchoose index r₀ lo hi hlo hlohi hhi hrR hpos hreg U hU hne hUP
  have hrpos (a : ι) : 0 < r a := (hlo a).trans (hr a).1
  have hrr₀ (a : ι) : r a < r₀ a := (hr a).2.trans (hhi a)
  have hc (a : ι) : (curves a).carrier = circularBoundary ((curves a).index : M) (r a) := by
    simpa only [hindex] using hcarrier a
  have hreg' (a : ι) : circularCoordinateRegion ((curves a).index : M) (r a) ⊆
      (coordinateChart ((curves a).index : M)).target := by
    simp only [hindex]
    intro x hx
    apply hreg a
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (r a)^2 at hx
    change circularRadiusSquared (coordinateChart (index a : M) (index a)) x ≤ (r₀ a)^2
    exact hx.trans (by nlinarith [hrpos a,hrr₀ a])
  have hsubset : boundaryCrossingSet curves univ ⊆ circularCrossingSet (fun a => (index a : M)) r := by
    rintro p ⟨a,_,b,_,hab,hpa,hpb⟩
    apply mem_iUnion.mpr
    exact ⟨⟨(a,b),hab⟩,by rw [← hcarrier a,← hcarrier b]; exact ⟨hpa,hpb⟩⟩
  let d : CircularFamilyGeometry A ι := {
    curves := curves, radius := r, outerRadius := r₀, chartRadius := r₀,
    linearPart := ell, convexPart := L,
    radius_pos := hrpos,
    radius_outer := fun a => by nlinarith [hrpos a,hrr₀ a],
    radius_chart := hrr₀,
    weight_positive := fun a => by simpa only [hindex] using hpos a,
    region := hreg', carrier := hc,
    cover := fun a => by simpa only [hindex] using hcover a,
    first_coordinate := fun a => by simpa only [hindex] using hphase a,
    pair_finite := fun a b hab => hcross.subset (fun p hp => hsubset
      (boundaryCrossingSet_pair curves (mem_univ a) (mem_univ b) hab hp.1 hp.2)),
    triple_empty := htriple,
    tangencies_finite := fun a b => by simpa only [hindex] using htan a b,
    independent := by
      intro a b hab p hp hpa hpb
      simpa only [hindex] using hind a b hab p (hsubset hp)
        (by simpa only [hindex] using hpa) (by simpa only [hindex] using hpb) }
  exact ⟨d,hell,hr,hindex,rfl,rfl,rfl⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
