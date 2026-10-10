import Mathlib

namespace OAI

/-! # Coercivity of a quadratic envelope with bounded sources -/

open Set Metric
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X]

theorem quadratic_envelope_coercive (p : X) {R t B A : ℝ} (hR : 0 ≤ R)
    (ht : 0 < t) (point : Y → X) (F : Y → ℝ) (hF : ∀ a, F a ≤ B)
    (hd : ∀ a, dist p (point a) ≤ R) (Φ : X → ℝ)
    (hΦ : ∀ x, ∃ a, Φ x = dist x (point a) ^ 2 / 2 - t * F a + t * A)
    (M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, L ≤ dist p x → M ≤ Φ x := by
  let L := R + |M| + t * |B| + t * |A| + 2
  refine ⟨L, by dsimp [L]; positivity, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hΦ x
  have htri := dist_triangle p (point a) x
  have hda := hd a
  rw [dist_comm (point a) x] at htri
  have hFB : t * F a ≤ t * |B| :=
    mul_le_mul_of_nonneg_left ((hF a).trans (le_abs_self B)) ht.le
  have hAA : -(t * |A|) ≤ t * A := by
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le A) ht.le]
  have hMM := le_abs_self M
  have hsq := sq_nonneg (dist x (point a) - 1)
  dsimp [L] at hx
  rw [ha]
  nlinarith

end RegularPointCoordinates

end OAI
