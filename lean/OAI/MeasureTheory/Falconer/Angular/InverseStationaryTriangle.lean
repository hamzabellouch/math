import OAI.MeasureTheory.Falconer.Angular.InverseStationaryCancellation

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseStationaryOperator_cancellation_reverse (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ j ∈ Finset.range (n+1),
      directStationaryOperator (n-j) (inverseStationaryOperator j f) x) =
        if n = 0 then f x else 0 := by
  rw [← inverseStationaryOperator_cancellation n hf x,
    ← Finset.sum_range_reflect (fun h =>
      directStationaryOperator h (inverseStationaryOperator (n-h) f) x) (n+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
  simp [Nat.sub_sub_self hj']

theorem inverseStationaryOperator_triangle_reverse (n : ℕ) (z : ℂ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ j ∈ Finset.range (n+1), ∑ h ∈ Finset.range (n+1-j),
      z^(j+h) * directStationaryOperator h (inverseStationaryOperator j f) x) = f x := by
  rw [← Finset.sum_range_diag_flip]
  have he : ∀ k ∈ Finset.range (n+1),
      (∑ j ∈ Finset.range (k+1),
        z^(j+(k-j)) * directStationaryOperator (k-j) (inverseStationaryOperator j f) x) =
          z^k * (if k = 0 then f x else 0) := by
    intro k hk
    rw [← inverseStationaryOperator_cancellation_reverse k hf x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [Nat.add_sub_of_le hj']
  rw [Finset.sum_congr rfl he]
  simp

end PlanarFalconer

end OAI
