import OAI.Geometry.SurfaceImmersion.Geometry.GenericSurfaceLevels
import OAI.Geometry.SurfaceImmersion.Correction.SmoothCircularRadius

namespace OAI

/-! Independent genuine disk radii can be chosen in every prescribed
positive box, with finite pair crossings and no triple crossings. The
regular-value statement is retained for the actual smooth radius fields. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_generic_circular_radii
    (index : ι → A.centers) (r0 lo hi : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hlohi : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < r0 i)
    (hpos : ∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r0 i)) :
    ∃ r : ι → ℝ, (∀ i, lo i < r i ∧ r i < hi i) ∧
      (∀ i j, i ≠ j → (circularBoundary (index i : M) (r i) ∩
        circularBoundary (index j : M) (r j)).Finite) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        circularBoundary (index i : M) (r i) ∩ circularBoundary (index j : M) (r j) ∩
          circularBoundary (index k : M) (r k) = ∅) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularBoundary (index i : M) (r i) ∩
          circularBoundary (index j : M) (r j),
        ∃ q : M, p ∈ (chartAt Plane q).source ∧
          Function.Surjective (fderiv ℝ (fun y => radiusPairProjection i j
            (fun k => A.circularRadiusField (index k) ((chartAt Plane q).symm y)))
            (chartAt Plane q p))) := by
  let U : Set (ι → ℝ) := {s | ∀ i, (lo i)^2 < s i ∧ s i < (hi i)^2}
  have hU : IsOpen U := by
    have heq : U = ⋂ i, {s : ι → ℝ | (lo i)^2 < s i ∧ s i < (hi i)^2} := by
      ext s
      simp only [mem_iInter,mem_ofPred_eq]
      rfl
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  have hUexists : U.Nonempty := by
    refine ⟨fun i => ((lo i)^2+(hi i)^2)/2,?_⟩
    intro i
    have hl := hlo i
    have hh := hlohi i
    constructor <;> nlinarith
  obtain ⟨s,hs,hfinite,htriple,hregular⟩ := exists_generic_surface_levels A
    (fun i => A.circularRadiusField (index i)) (fun i => A.circularRadiusField_smooth (index i))
    U hU hUexists
  let r : ι → ℝ := fun i => Real.sqrt (s i)
  have hspos (i : ι) : 0 < s i := (sq_nonneg (lo i)).trans_lt (hs i).1
  have hrsq (i : ι) : (r i)^2 = s i := Real.sq_sqrt (hspos i).le
  have hrpos (i : ι) : 0 < r i := Real.sqrt_pos.mpr (hspos i)
  have hb (i : ι) : lo i < r i ∧ r i < hi i := by
    have hl := hlo i
    have hh := hlohi i
    have hsq := hrsq i
    have hposr := hrpos i
    have hs' := hs i
    constructor <;> nlinarith
  have hsmall (i : ι) : (r i)^2 < (r0 i)^2 := by
    have h1 := (hb i).2
    have h2 := hhi i
    have h3 := hrpos i
    nlinarith
  have heval (i : ι) {p : M} (hp : p ∈ circularBoundary (index i : M) (r i)) :
      A.circularRadiusField (index i) p = s i :=
    (A.circularBoundary_radiusField (index i) (hsmall i) (hpos i) hp).trans (hrsq i)
  refine ⟨r,hb,?_,?_,?_⟩
  · intro i j hij
    exact (hfinite i j hij).subset (fun p hp => ⟨heval i hp.1,heval j hp.2⟩)
  · intro i j k hij hik hjk
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact htriple i j k hij hik hjk p ⟨heval i hp.1.1,heval j hp.1.2,heval k hp.2⟩
  · intro i j hij p hp
    exact hregular i j hij p (heval i hp.1) (heval j hp.2)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
