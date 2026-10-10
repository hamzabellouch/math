import OAI.Geometry.RCD.Coordinates.MeasuredCoordinateInput
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! # Measurable representatives of pointed metric approximations

A finite net and the first admissible index replace an arbitrary pointed
approximation by a measurable one, with a controlled loss in its error.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A compact set admits a measurable nearest-net choice at any positive
accuracy. No measurability of a subsequent map on the net is needed. -/
theorem exists_measurable_net_choice {s : Set X} (hs : IsCompact s)
    (hne : s.Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℕ → X, ∃ j : X → ℕ, Measurable j ∧
      ∀ x ∈ s, c (j x) ∈ s ∧ dist x (c (j x)) < η := by
  classical
  obtain ⟨t, hts, ht, hcover⟩ := hs.finite_cover_balls hη
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, _⟩ := mem_iUnion₂.mp (hcover hx)
    exact ⟨y, hy⟩
  obtain ⟨c, hc⟩ := ht.countable.exists_eq_range htne
  let P (x : X) (i : ℕ) : Prop := x ∉ s ∨ dist x (c i) < η
  have hP (x : X) : ∃ i, P x i := by
    by_cases hx : x ∈ s
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
      obtain ⟨i, rfl⟩ := hc ▸ hy
      exact ⟨i, Or.inr hxy⟩
    · exact ⟨0, Or.inl hx⟩
  refine ⟨c, fun x => Nat.find (hP x), measurable_find hP ?_, ?_⟩
  · intro i
    exact hs.isClosed.measurableSet.compl.union
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).measurableSet
  · intro x hx
    refine ⟨hts (hc ▸ mem_range_self _), ?_⟩
    exact (Nat.find_spec (hP x)).resolve_left (not_not.mpr hx)

variable [ProperSpace X]

/-- Pointed approximations can be chosen measurable at the price of a
fixed error factor. This concerns the actual maps on the whole space. -/
theorem IsPointedApproximation.exists_measurable {Y : Type*}
    [MetricSpace Y] [MeasurableSpace Y] {p : X} {q : Y} {r R ε : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hε : 0 < ε) {f : X → Y}
    (hf : IsPointedApproximation p q r R ε f) :
    ∃ g : X → Y, Measurable g ∧ IsPointedApproximation p q r R (5 * ε) g := by
  obtain ⟨c, j, hj, hnet⟩ := exists_measurable_net_choice
    (isCompact_closedBall p (R*r)) ⟨p, by simp [mul_nonneg hR.le hr.le]⟩
    (mul_pos hε hr)
  let g := fun x => f (c (j x))
  have hgm : Measurable g := (measurable_of_countable (f ∘ c)).comp hj
  have hclose (x : X) (hx : dist x p ≤ R*r) : dist (g x) (f x) ≤ 2*ε := by
    obtain ⟨hc, hxc⟩ := hnet x hx
    have hdist := (abs_le.mp (hf.2.1 (c (j x)) x hc hx)).2
    have hsmall : dist (c (j x)) x / r < ε := by
      rw [div_lt_iff₀ hr, dist_comm]
      exact hxc
    dsimp only [g]
    linarith
  refine ⟨g, hgm, ?_, ?_, ?_⟩
  · have hp := hclose p (by simp [mul_nonneg hR.le hr.le])
    have htri := dist_triangle (g p) (f p) q
    linarith [hf.1]
  · intro x y hx hy
    have htri : |dist (g x) (g y) - dist (f x) (f y)| ≤
        dist (g x) (f x) + dist (g y) (f y) := by
      have h1 := dist_triangle4 (g x) (f x) (f y) (g y)
      have h2 := dist_triangle4 (f x) (g x) (g y) (f y)
      rw [dist_comm (f y) (g y)] at h1
      rw [dist_comm (f x) (g x)] at h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hbase := hf.2.1 x y hx hy
    have hsum := abs_add_le (dist (g x) (g y) - dist (f x) (f y))
      (dist (f x) (f y) - dist x y / r)
    have hx' := hclose x hx
    have hy' := hclose y hy
    have heq : dist (g x) (g y) - dist (f x) (f y) +
        (dist (f x) (f y) - dist x y / r) = dist (g x) (g y) - dist x y / r := by ring
    rw [heq] at hsum
    linarith
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hf.2.2 y (by linarith)
    refine ⟨x, hx, ?_⟩
    have htri := dist_triangle (g x) (f x) y
    linarith [hclose x hx]

end RegularPointCoordinates

end

end OAI
