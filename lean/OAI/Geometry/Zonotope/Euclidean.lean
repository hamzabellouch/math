import OAI.Geometry.Zonotope.Scaling
import OAI.Geometry.Zonotope.Body
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Coordinate and Euclidean versions of the explicit centered zonotope. -/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

/-- The actual scalar image of the cube-plus-diagonal body in Euclidean space. -/
def euclidean (c : ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.toLp 2 '' ((fun y : ι → ℝ => c • y) '' centered)

/-- The directional support value, before multiplication by the scale. -/
def support (u : ι → ℝ) : ℝ := ((∑ i, |u i|) + |∑ i, u i|) / 2

lemma support_zero : support (0 : ι → ℝ) = 0 := by simp [support]

lemma support_smul (u : ι → ℝ) (a : ℝ) : support (a • u) = |a| * support u :=
  support_value_smul u a

lemma inner_eq_coordinates (u x : EuclideanSpace ℝ ι) :
    ⟪u, x⟫ = ∑ i, u i * x i := by
  simp only [PiLp.inner_apply, Real.inner_apply]

omit [Fintype ι] in
lemma mem_euclidean_iff (c : ℝ) (x : EuclideanSpace ℝ ι) :
    x ∈ euclidean c ↔ WithLp.ofLp x ∈ (fun y : ι → ℝ => c • y) '' centered := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hx
    exact ⟨WithLp.ofLp x, hx, rfl⟩

/-- All directional inequalities characterize this concrete Euclidean body. -/
theorem euclidean_eq_halfspaces [DecidableEq ι] (c : ℝ) (hc : 0 < c) :
    (euclidean c : Set (EuclideanSpace ℝ ι)) =
      {x | ∀ u : EuclideanSpace ℝ ι, ⟪u, x⟫ ≤ c * support (WithLp.ofLp u)} := by
  ext x
  rw [mem_euclidean_iff, scaled_centered_eq_support_halfspaces c hc]
  constructor
  · intro hx u
    simpa only [inner_eq_coordinates, support] using hx (WithLp.ofLp u)
  · intro hx u
    simpa only [inner_eq_coordinates, support] using hx (WithLp.toLp 2 u)

/-- Every directional support inequality is attained by an explicit point. -/
theorem euclidean_support_attained (c : ℝ) (u : EuclideanSpace ℝ ι) :
    ∃ x ∈ euclidean c, ⟪u, x⟫ = c * support (WithLp.ofLp u) := by
  obtain ⟨x, hx, heq⟩ := scaled_centered_support_attained (WithLp.ofLp u) c
  refine ⟨WithLp.toLp 2 x, ⟨x, hx, rfl⟩, ?_⟩
  simpa only [inner_eq_coordinates, support] using heq

lemma isCompact_euclidean (c : ℝ) : IsCompact (euclidean c : Set (EuclideanSpace ℝ ι)) :=
  (isCompact_scaled_centered c).image (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))

lemma convex_euclidean (c : ℝ) : Convex ℝ (euclidean c : Set (EuclideanSpace ℝ ι)) :=
  (convex_scaled_centered c).linear_image
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toLinearMap

lemma euclidean_interior_nonempty (c : ℝ) (hc : c ≠ 0) :
    (interior (euclidean c : Set (EuclideanSpace ℝ ι))).Nonempty := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toHomeomorph
  have he : (euclidean c : Set (EuclideanSpace ℝ ι)) =
      e '' ((fun y : ι → ℝ => c • y) '' centered) := rfl
  rw [he, ← e.image_interior]
  exact (scaled_centered_interior_nonempty c hc).image _

end DiagonalZonotope

end

end OAI
