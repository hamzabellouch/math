import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem near_support_radius_power_le_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (hμ : μ.support.Nonempty) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ a ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball a r))
    (x : Ambient d) (δ : ℝ) (hδ : 0 < δ) (hadm : AdmissibleRadius μ (δ / 256))
    (hnear : infDist x μ.support ≤ δ / 512) :
    (ENNReal.ofReal δ) ^ n ≤
      ENNReal.ofReal (C * 256 ^ n) * μ (closedBall x (δ / 128)) := by
  obtain ⟨a, ha, hdist⟩ := μ.isClosed_support.exists_infDist_eq_dist hμ x
  have hxa : dist x a ≤ δ / 512 := by rw [← hdist]; exact hnear
  have hsub : ball a (δ / 256) ⊆ closedBall x (δ / 128) := by
    intro y hy
    have hya : dist y a < δ / 256 := hy
    have ht := dist_triangle y a x
    rw [dist_comm a x] at ht
    change dist y x ≤ δ / 128
    linarith
  have hl := (hlower a ha (δ / 256) hadm).trans (measure_mono hsub)
  have heq : (ENNReal.ofReal δ) ^ n =
      ENNReal.ofReal (C * 256 ^ n) * ENNReal.ofReal ((δ / 256) ^ n / C) := by
    rw [← ENNReal.ofReal_pow hδ.le, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * 256 ^ n)]
    congr 1
    rw [div_pow]
    field_simp
  rw [heq]
  exact mul_le_mul_right hl _

end

end RieszRectifiability

end OAI
