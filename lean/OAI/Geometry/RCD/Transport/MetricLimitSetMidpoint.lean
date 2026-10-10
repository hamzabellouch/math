import OAI.Geometry.RCD.Transport.MetricSetMidpointLaw
import OAI.Geometry.RCD.Transport.MetricLimitMidpointContraction
import OAI.Geometry.RCD.Sobolev.WeakMinMass
import OAI.Geometry.RCD.Transport.MidpointMinCoefficientLimit

namespace OAI

/-! # The two-source midpoint inequality for the actual weak metric limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_set_midpoint_enlarged {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S ρ σ η κ : ℝ} (hS : 0 < S) (hρ : 0 ≤ ρ) (hρS : ρ < S)
    (hσρ : σ < ρ) (hκ : 0 < κ) (z : Euclidean n)
    {A B : Set (Euclidean n)} (hA : IsOpen A) (hB : IsOpen B)
    (hAsub : A ⊆ closedBall z η) (hBsub : B ⊆ closedBall z η)
    (hAnorm : ∀ a ∈ A, ‖a‖ ≤ σ) (hBnorm : ∀ b ∈ B, ‖b‖ ≤ σ)
    (hroom : ρ+2*η < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q)) :
    min ((Q : Measure (Euclidean n)).real A) ((Q : Measure (Euclidean n)).real B) ≤
      (Q : Measure (Euclidean n)).real (cthickening κ (midpointSet A B)) := by
  by_cases hApos : 0 < (Q : Measure (Euclidean n)).real A
  swap
  · exact (min_le_left _ _).trans ((le_of_not_gt hApos).trans measureReal_nonneg)
  by_cases hBpos : 0 < (Q : Measure (Euclidean n)).real B
  swap
  · exact (min_le_right _ _).trans ((le_of_not_gt hBpos).trans measureReal_nonneg)
  let P := fun k => normalizedBallPushforward (hausdorff n X) (p k) (r k) S (V k) (hfin k)
  have hpos (k : ℕ) : 0 < (hausdorff n X).real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hfin k)
  have hcoef := midpoint_min_coefficient_tendsto_one hn hK (fun k => (hr k).le) hε hcurv (d := 2*ρ)
  have herror : Tendsto (fun k => Real.sqrt (2*(ε k*(4*ρ+ε k)))) atTop (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (2*(t*(4*ρ+t)))) := by fun_prop
    simpa only [Function.comp_def,mul_zero,zero_mul,Real.sqrt_zero] using (hc.tendsto 0).comp hε
  have hAP := probability_open_eventual_lower hlim hA (half_lt_self hApos)
  have hBP := probability_open_eventual_lower hlim hB (half_lt_self hBpos)
  have hresult := probability_open_closed_min_contraction hlim hA hB
    (isClosed_cthickening : IsClosed (cthickening κ (midpointSet A B))) zero_lt_one hcoef
  simp only [one_mul] at hresult
  apply hresult
  filter_upwards [hAP,hBP,herror.eventually (Iio_mem_nhds hκ),
    hε.eventually (Iio_mem_nhds (show (0:ℝ)<(ρ-σ)/2 by linarith only [hσρ])),
    hε.eventually (Iio_mem_nhds (show (0:ℝ)<S-(ρ+2*η) by linarith only [hroom]))]
    with k hkA hkB hkerr hksmall hkroom
  have hA0 := normalizedBallPushforward_preimage_ne_zero _ (p k) (r k) S (V k)
    (hfin k) (hpos k) (hVm k) hA.measurableSet ((half_pos hApos).trans_le hkA)
  have hB0 := normalizedBallPushforward_preimage_ne_zero _ (p k) (r k) S (V k)
    (hfin k) (hpos k) (hVm k) hB.measurableSet ((half_pos hBpos).trans_le hkB)
  have he0 : 0 ≤ ε k := dist_nonneg.trans (hV k).1
  have hm := hX.metric_set_midpoint_law hn (hr k) hS hρ hρS he0 (by linarith only [hkroom])
    (V k) (hVm k) (hV k) hA.measurableSet hB.measurableSet z hAsub hBsub
    (fun a ha => by linarith only [hAnorm a ha,hksmall])
    (fun b hb => by linarith only [hBnorm b hb,hksmall]) hA0 hB0 (hfin k)
  exact hm.trans (measureReal_mono (cthickening_mono hkerr.le _) (measure_ne_top _ _))

end RegularPointCoordinates

end

end OAI
