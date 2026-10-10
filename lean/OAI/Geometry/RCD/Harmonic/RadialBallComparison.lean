import OAI.Geometry.RCD.Transport.AnnularTransportComparison
import OAI.Geometry.RCD.Transport.RadialDistortionContinuity

namespace OAI

/-! # Removing the auxiliary center radius in radial CD comparison

The small initial ball in the actual transport argument shrinks to the
pole. Continuity of the sharp distortion coefficient gives a comparison
at every radius, without selecting continuity radii of the measure.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem FullCD.ball_contraction_below
    (μ : Measure X) [SigmaFinite μ] {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : K < 0) (p : X) {r R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) (ht1 : t < 1) (htr : t * R < r) :
    tau K n t R ^ n * μ (ball p R) ≤ μ (ball p r) := by
  have hmap : Tendsto (fun δ : ℝ => (t, R + δ)) (𝓝[>] 0) (𝓝 (t, R)) := by
    have hh : Tendsto (fun δ : ℝ => R + δ) (𝓝[>] 0) (𝓝 R) := by
      have hzero : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [add_zero] using hzero.const_add R
    exact tendsto_const_nhds.prodMk_nhds hh
  have hc := (continuousAt_tau_nat_power_of_neg hK hn ht ht1 hR).tendsto.comp hmap
  have hm := (ENNReal.continuous_mul_const (hfin (ball p R) isBounded_ball).ne).continuousAt.tendsto.comp hc
  apply le_of_tendsto hm
  have hε : 0 < (r - t * R) / (1 + t) := div_pos (sub_pos.mpr htr) (by linarith)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε)] with δ hδ hsmall
  have houter : t * R + (1 + t) * δ < r := by
    have hh := (lt_div_iff₀ (by linarith : 0 < 1 + t)).mp hsmall
    nlinarith only [hh]
  exact (hcd.ball_contraction_with_center_error μ hpos hfin hn hK.le p hR hδ ht ht1).trans
    (measure_mono (ball_subset_ball houter.le))

theorem FullCD.radial_ball_ratio
    (μ : Measure X) [SigmaFinite μ] {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : K < 0) (p : X) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    tau K n (r / R) R ^ n * μ (ball p R) ≤ μ (ball p r) := by
  have hR : 0 < R := hr.trans_le hrR
  by_cases heq : r = R
  · subst r
    simp [hR.ne', tau]
  have hrR' : r < R := lt_of_le_of_ne hrR heq
  have hq : 0 < r / R := div_pos hr hR
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR'
  have hmap : Tendsto (fun t : ℝ => (t, R)) (𝓝[<] (r / R)) (𝓝 (r / R, R)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds tendsto_const_nhds
  have hc := (continuousAt_tau_nat_power_of_neg hK hn hq hq1 hR).tendsto.comp hmap
  have hm := (ENNReal.continuous_mul_const (hfin (ball p R) isBounded_ball).ne).continuousAt.tendsto.comp hc
  apply le_of_tendsto hm
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hq)] with t htq ht
  exact hcd.ball_contraction_below μ hpos hfin hn hK p hR ht (htq.trans hq1)
    ((lt_div_iff₀ hR).mp htq)

end RegularPointCoordinates

end OAI
