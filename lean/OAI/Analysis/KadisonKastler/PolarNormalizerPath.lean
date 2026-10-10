import OAI.Analysis.KadisonKastler.QuantitativePolarPath
import OAI.Analysis.KadisonKastler.NormalizerDefect

namespace OAI

/-! # Polar paths preserve approximate algebra relations -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_unitary_bilinear_error (v : unitary (H →L[ℂ] H))
    (a c x : H →L[ℂ] H) {p q r : ℝ} (hp : 0 ≤ p)
    (hva : ‖(v : H →L[ℂ] H) - a‖ ≤ p)
    (hvc : ‖star (v : H →L[ℂ] H) - c‖ ≤ q)
    (hc : ‖c‖ ≤ 1 + r) (hx : ‖x‖ ≤ 1) :
    ‖unitaryConj (H := H) v x - a * x * c‖ ≤ p * (1 + r) + q := by
  have he : unitaryConj (H := H) v x - a * x * c =
      ((v : H →L[ℂ] H) - a) * x * c + (v : H →L[ℂ] H) * x * (star (v : H →L[ℂ] H) - c) := by
    simp only [unitaryConj, sub_mul, mul_sub, mul_assoc]
    abel
  have hleft : ‖((v : H →L[ℂ] H) - a) * x‖ ≤ p := by
    exact (norm_mul_le _ _).trans ((mul_le_mul hva hx (norm_nonneg _) hp).trans_eq
      (mul_one _))
  have hleft' : ‖((v : H →L[ℂ] H) - a) * x * c‖ ≤ p * (1 + r) :=
    (norm_mul_le _ _).trans (mul_le_mul hleft hc (norm_nonneg _) hp)
  have hright : ‖(v : H →L[ℂ] H) * x * (star (v : H →L[ℂ] H) - c)‖ ≤ q := by
    rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul hx hvc (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _))
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hleft' hright)

theorem infDist_polar_conjugation_le (M : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (a c x : H →L[ℂ] H) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hva : ‖(v : H →L[ℂ] H) - a‖ ≤ 4 * r)
    (hvc : ‖star (v : H →L[ℂ] H) - c‖ ≤ 10 * r)
    (hc : ‖c‖ ≤ 1 + r) (hx : ‖x‖ ≤ 1)
    (halg : Metric.infDist (a * x * c) (M : Set (H →L[ℂ] H)) ≤ r) :
    Metric.infDist (unitaryConj (H := H) v x) (M : Set (H →L[ℂ] H)) ≤ 16 * r := by
  have h := Metric.infDist_le_infDist_add_dist
    (x := unitaryConj (H := H) v x) (y := a * x * c) (s := (M : Set (H →L[ℂ] H)))
  rw [dist_eq_norm] at h
  have hn := norm_unitary_bilinear_error v a c x (show 0 ≤ 4 * r by positivity)
    hva hvc hc hx
  exact h.trans ((add_le_add halg hn).trans (by nlinarith))

theorem infDist_polar_star_conjugation_le (M : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (a c x : H →L[ℂ] H) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hva : ‖(v : H →L[ℂ] H) - a‖ ≤ 4 * r)
    (hvc : ‖star (v : H →L[ℂ] H) - c‖ ≤ 10 * r)
    (ha : ‖a‖ ≤ 1 + r) (hx : ‖x‖ ≤ 1)
    (halg : Metric.infDist (c * x * a) (M : Set (H →L[ℂ] H)) ≤ r) :
    Metric.infDist (unitaryConj (H := H) (star v) x) (M : Set (H →L[ℂ] H)) ≤ 17 * r := by
  have hn := norm_unitary_bilinear_error (star v) c a x
    (show 0 ≤ 10 * r by positivity) hvc
    (by simpa only [Unitary.coe_star, star_star] using hva) ha hx
  have h := Metric.infDist_le_infDist_add_dist
    (x := unitaryConj (H := H) (star v) x) (y := c * x * a) (s := (M : Set (H →L[ℂ] H)))
  rw [dist_eq_norm] at h
  exact h.trans ((add_le_add halg hn).trans (by nlinarith))

end

end KadisonKastler

end OAI
