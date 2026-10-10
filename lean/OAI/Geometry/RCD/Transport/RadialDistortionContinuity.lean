import OAI.Geometry.RCD.Transport.HyperbolicDistortion

namespace OAI

/-! # Continuity of the exact CD radial volume coefficient -/

open Set Filter
open scoped ENNReal Topology

namespace RegularPointCoordinates

theorem continuousAt_tau_nat_power_of_neg {K t R : ℝ} {n : ℕ}
    (hK : K < 0) (hn : 2 ≤ n) (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    ContinuousAt (fun q : ℝ × ℝ => tau K n q.1 q.2 ^ n) (t, R) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hK) (sub_pos.mpr hn1))
  let F : ℝ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal q.1 *
    ENNReal.ofReal (Real.sinh (q.1 * q.2 * a) / Real.sinh (q.2 * a)) ^ (n - 1)
  have hratio : ContinuousAt
      (fun q : ℝ × ℝ => Real.sinh (q.1 * q.2 * a) / Real.sinh (q.2 * a)) (t, R) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sinh_pos_iff.mpr (mul_pos hR ha)).ne'
  have hF : ContinuousAt F (t, R) := by
    have hp : ContinuousAt (fun q : ℝ × ℝ =>
        ENNReal.ofReal (Real.sinh (q.1 * q.2 * a) / Real.sinh (q.2 * a)) ^ (n - 1))
        (t, R) := by
      simpa only [ENNReal.rpow_natCast, Function.comp_def] using
        (ENNReal.continuous_rpow_const (y := ((n - 1 : ℕ) : ℝ))).continuousAt.comp
          (ENNReal.continuous_ofReal.continuousAt.comp hratio)
    exact ENNReal.Tendsto.mul
      (ENNReal.continuous_ofReal.comp continuous_fst).continuousAt
      (Or.inl (ENNReal.ofReal_pos.mpr ht).ne') hp (Or.inr ENNReal.ofReal_ne_top)
  apply hF.congr_of_eventuallyEq
  have hlow : ∀ᶠ q : ℝ × ℝ in 𝓝 (t, R), 0 < q.1 :=
    continuous_fst.continuousAt.eventually (Ioi_mem_nhds ht)
  have hupp : ∀ᶠ q : ℝ × ℝ in 𝓝 (t, R), q.1 < 1 :=
    continuous_fst.continuousAt.eventually (Iio_mem_nhds ht1)
  have hr : ∀ᶠ q : ℝ × ℝ in 𝓝 (t, R), 0 < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hR)
  filter_upwards [hlow, hupp, hr] with q hq hq1 hqR
  rw [tau_nat_power hn hq hq1, sigma_neg_eq hK hn1 hqR]

end RegularPointCoordinates

end OAI
