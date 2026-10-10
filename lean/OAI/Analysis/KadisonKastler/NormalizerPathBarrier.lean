import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace OAI

/-! # The continuous barrier in the approximate-normalizer path argument -/

namespace KadisonKastler

theorem continuous_quadratic_barrier {I : Set ℝ} (hI : IsPreconnected I)
    (hzero : 0 ∈ I) (b : ℝ → ℝ) (hb : ContinuousOn b I) (hbzero : b 0 = 0)
    (hnonneg : ∀ t ∈ I, 0 ≤ b t) {A L r : ℝ}
    (hA : A < r / 2) (hL : 0 ≤ L) (hr : 0 < r) (hLr : L * r ≤ 1 / 2)
    (hquad : ∀ t ∈ I, b t < 2 * r → b t ≤ A + L * (b t) ^ 2) :
    ∀ t ∈ I, b t ≤ 2 * A := by
  have hsmall : ∀ t ∈ I, b t < r := by
    intro t ht
    by_contra hnot
    have hrt : r ≤ b t := le_of_not_gt hnot
    obtain ⟨s, hs, hsr⟩ := hI.intermediate_value₂ hzero ht hb continuousOn_const
      (show b 0 ≤ r by rw [hbzero]; exact hr.le) hrt
    have hq := hquad s hs (by rw [hsr]; linarith)
    rw [hsr] at hq
    have hbound := mul_le_mul_of_nonneg_right hLr hr.le
    nlinarith
  intro t ht
  have hbt := hsmall t ht
  have hq := hquad t ht (by linarith)
  have hb0 := hnonneg t ht
  have hlinear : L * b t ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hbt.le hL).trans hLr
  have hbound := mul_le_mul_of_nonneg_right hlinear hb0
  nlinarith

end KadisonKastler

end OAI
