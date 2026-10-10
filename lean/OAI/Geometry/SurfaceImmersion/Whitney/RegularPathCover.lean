import OAI.Geometry.SurfaceImmersion.Whitney.RegularArcPaths

namespace OAI

/-! A finite closed-interval cover records actual smooth arc formulas for
paths assembled by subdivision and concatenation. Slopes may be zero before
injectivity of the assembled path is imposed. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

structure RegularPathCover {x y : M} (γ : Path x y) where
  Index : Type
  finite : Fintype Index
  region : Index → Set ℝ
  closed : ∀ i, IsClosed (region i)
  convex : ∀ i, Convex ℝ (region i)
  subset : ∀ i, region i ⊆ Icc 0 1
  arc : Index → SmoothCompactArc J M
  slope : Index → ℝ
  offset : Index → ℝ
  cover : ∀ t : I, ∃ i, (t:ℝ) ∈ region i
  parameter : ∀ i t, t ∈ region i → slope i*t+offset i ∈ Icc (arc i).start (arc i).finish
  agree : ∀ i (t : I), (t:ℝ) ∈ region i → γ t = (arc i).curve (slope i*t+offset i)

namespace RegularPathCover

lemma affine_preimage_convex {S : Set ℝ} (hS : Convex ℝ S) (a b : ℝ) :
    Convex ℝ ((fun x => a*x+b) ⁻¹' S) := by
  intro x hx y hy u v hu hv huv
  have h := hS hx hy hu hv huv
  change a*(u*x+v*y)+b ∈ S
  have he : a*(u*x+v*y)+b = u*(a*x+b)+v*(a*y+b) := by
    calc
      a*(u*x+v*y)+b = a*(u*x+v*y)+(u+v)*b := by rw [huv,one_mul]
      _ = u*(a*x+b)+v*(a*y+b) := by ring
  rw [he]
  exact h

noncomputable def ofArc (P : SmoothCompactArc J M) : RegularPathCover (J := J) P.path where
  Index := Unit
  finite := inferInstance
  region := fun _ => Icc 0 1
  closed := fun _ => isClosed_Icc
  convex := fun _ => convex_Icc 0 1
  subset := fun _ => Subset.rfl
  arc := fun _ => P
  slope := fun _ => P.finish-P.start
  offset := fun _ => P.start
  cover := fun t => ⟨(),t.property⟩
  parameter := by
    intro _ t ht
    have h := ((iccHomeoI P.start P.finish P.start_lt_finish).symm ⟨t,ht⟩).property
    simpa only [iccHomeoI_symm_apply_coe] using h
  agree := by
    intro _ t _
    change P.curve (((iccHomeoI P.start P.finish P.start_lt_finish).symm t):ℝ) = _
    rw [iccHomeoI_symm_apply_coe]

variable {x y : M} {γ : Path x y}

noncomputable def cast (P : RegularPathCover (J := J) γ) {x' y' : M}
    (hx : x' = x) (hy : y' = y) : RegularPathCover (J := J) (γ.cast hx hy) where
  Index := P.Index
  finite := P.finite
  region := P.region
  closed := P.closed
  convex := P.convex
  subset := P.subset
  arc := P.arc
  slope := P.slope
  offset := P.offset
  cover := P.cover
  parameter := P.parameter
  agree := P.agree

noncomputable def subpath (P : RegularPathCover (J := J) γ) (s t : I) :
    RegularPathCover (J := J) (γ.subpath s t) := by
  let a : ℝ := (t:ℝ)-(s:ℝ)
  let b : ℝ := s
  have haff (u : I) : a*(u:ℝ)+b = (Icc.convexComb s t u : ℝ) := by
    rw [Icc.coe_convexComb]
    dsimp [a,b]
    ring
  refine {
    Index := P.Index
    finite := P.finite
    region := fun i => Icc 0 1 ∩ (fun u => a*u+b) ⁻¹' P.region i
    closed := fun i => isClosed_Icc.inter ((P.closed i).preimage (by fun_prop))
    convex := fun i => (convex_Icc 0 1).inter (affine_preimage_convex (P.convex i) a b)
    subset := fun _ => inter_subset_left
    arc := P.arc
    slope := fun i => P.slope i*a
    offset := fun i => P.slope i*b+P.offset i
    cover := ?_
    parameter := ?_
    agree := ?_ }
  · intro u
    obtain ⟨i,hi⟩ := P.cover (Icc.convexComb s t u)
    refine ⟨i,u.property,?_⟩
    change a*(u:ℝ)+b ∈ P.region i
    rw [haff u]
    exact hi
  · intro i u hu
    have h := P.parameter i (a*u+b) hu.2
    convert h using 1; ring
  · intro i u hu
    have hmem : (Icc.convexComb s t u : ℝ) ∈ P.region i := by
      rw [← haff u]
      exact hu.2
    have h := P.agree i (Icc.convexComb s t u) hmem
    change γ (Icc.convexComb s t u) = _
    rw [h,← haff u]
    congr 1
    ring

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
