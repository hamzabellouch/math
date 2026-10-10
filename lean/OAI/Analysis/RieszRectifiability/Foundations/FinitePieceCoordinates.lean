import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.FiniteBallChartUnion

namespace OAI

/-!
# Coordinates selected from a Lipschitz ball cover

Choosing a preimage for each covered point produces coordinates in the parameter
ball. The Lipschitz bound on the covering map controls ambient distances by the
distances between these selected coordinates, without requiring continuity of
the selection.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_coordinates_of_lipschitz_ball_cover {n d : ℕ}
    (E : Set (Ambient d)) (r : ℝ) (f : ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hf : LipschitzWith M f) (hcover : E ⊆ Set.range f) :
    ∃ coord : Ambient d → Ambient n,
      (∀ x ∈ E, coord x ∈ ball (0 : Ambient n) r) ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (M : ℝ) * dist (coord x) (coord y) := by
  classical
  let pre : ∀ x : Ambient d, x ∈ E → ball (0 : Ambient n) r :=
    fun x hx => (hcover hx).choose
  have hpre (x : Ambient d) (hx : x ∈ E) : f (pre x hx) = x := (hcover hx).choose_spec
  let coord : Ambient d → Ambient n := fun x => if hx : x ∈ E then (pre x hx).val else 0
  have hcoord (x : Ambient d) (hx : x ∈ E) : coord x = (pre x hx).val := by
    simp only [coord, dite_eq_left hx]
  refine ⟨coord, ?_, ?_⟩
  · intro x hx
    rw [hcoord x hx]
    exact (pre x hx).property
  · intro x hx y hy
    have h := hf.dist_le_mul (pre x hx) (pre y hy)
    rw [hpre x hx, hpre y hy] at h
    simpa only [hcoord x hx, hcoord y hy, Subtype.dist_eq] using! h

def finitePartialCoordinateConstant (d N : ℕ) (M : ℝ≥0) : ℝ≥0 :=
  max 1 (finiteBallChartUnionConstant d N (lipschitzExtensionConstant (Ambient d) * M))

theorem finitePartialCoordinateConstant_ge_one (d N : ℕ) (M : ℝ≥0) :
    1 ≤ finitePartialCoordinateConstant d N M := le_max_left _ _

theorem exists_coordinates_of_finite_partial_charts {n d : ℕ} (hn : 0 < n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (D : Fin N → Set (Ambient n)) (hD : ∀ i, D i ⊆ ball (0 : Ambient n) r)
    (f : Fin N → Ambient n → Ambient d) (M : ℝ≥0)
    (hLip : ∀ i, LipschitzOnWith M (f i) (D i))
    (himage : ∀ i, f i '' D i ⊆ closedBall z (3 * r)) :
    ∃ coord : Ambient d → Ambient n,
      (∀ x ∈ ⋃ i : Fin N, f i '' D i, coord x ∈ closedBall (0 : Ambient n) r) ∧
      ∀ x ∈ ⋃ i : Fin N, f i '' D i, ∀ y ∈ ⋃ i : Fin N, f i '' D i,
        dist x y ≤ (finitePartialCoordinateConstant d N M : ℝ) * dist (coord x) (coord y) := by
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_finite_partial_charts hn N r hr z
    D hD f M hLip himage
  have hg' : LipschitzWith (finitePartialCoordinateConstant d N M) g := hg.weaken (le_max_right _ _)
  obtain ⟨coord, hball, hsep⟩ := exists_coordinates_of_lipschitz_ball_cover
    (⋃ i : Fin N, f i '' D i) r g (finitePartialCoordinateConstant d N M) hg' hcover
  exact ⟨coord, fun x hx => ball_subset_closedBall (hball x hx), hsep⟩

end

end RieszRectifiability

end OAI
