import OAI.Geometry.RCD.Transport.MetricLocalMidpointLaw
import OAI.Geometry.RCD.Transport.CurvatureMidpointLimit
import OAI.Geometry.RCD.Transport.WeakMidpointMass

namespace OAI

/-! # Local midpoint contraction for the actual weak metric-law limit

The proof passes the normalized CD inequality from the original spaces.
Open source balls and a closed enlarged target avoid a boundary assumption.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem normalizedBallPushforward_preimage_ne_zero {n : ℕ}
    (μ : Measure X) (p : X) (r S : ℝ) (V : X → Euclidean n)
    (hfin : μ (ball p (S*r)) ≠ ⊤) (hpos : 0 < μ.real (ball p (S*r)))
    (hVm : Measurable V) {A : Set (Euclidean n)} (hA : MeasurableSet A)
    (hP : 0 < (normalizedBallPushforward μ p r S V hfin : Measure (Euclidean n)).real A) :
    μ (V ⁻¹' A ∩ ball p (S*r)) ≠ 0 := by
  intro hz
  rw [normalizedBallPushforward_real μ p r S V hfin hpos hVm hA] at hP
  have he : μ.real (V ⁻¹' A ∩ ball p (S*r))=0 := by
    simp only [Measure.real,hz,ENNReal.toReal_zero]
  rw [he,mul_zero] at hP
  exact lt_irrefl 0 hP

theorem NoncollapsedRCD.metric_limit_midpoint_enlarged {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S ρ η a b κ : ℝ} (hS : 0 < S) (hρ : 0 ≤ ρ) (hρS : ρ < S)
    (hκ : 0 < κ)
    (x y z : Euclidean n) (hxa : ‖x‖+a < ρ) (hyb : ‖y‖+b < ρ)
    (hx : closedBall x a ⊆ closedBall z η) (hy : closedBall y b ⊆ closedBall z η)
    (hroom : ρ+2*η < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q))
    (hAx : 0 < (Q : Measure (Euclidean n)).real (ball x a))
    (hBy : 0 < (Q : Measure (Euclidean n)).real (ball y b)) :
    (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b) ≤
      (Q : Measure (Euclidean n)).real
        (closedBall ((1/2:ℝ) • (x+y)) ((a+b)/2+κ)) := by
  let P := fun k => normalizedBallPushforward (hausdorff n X)
    (p k) (r k) S (V k) (hfin k)
  have hpos (k : ℕ) : 0 < (hausdorff n X).real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hfin k)
  have hcoef := (midpointFloor_real_tendsto_half hn hK (fun k => (hr k).le) hε hcurv
    (d := 2*ρ)).pow n
  have herror : Tendsto (fun k => Real.sqrt (2*(ε k*(4*ρ+ε k)))) atTop (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (2*(t*(4*ρ+t)))) := by fun_prop
    simpa only [Function.comp_def,mul_zero,zero_mul,Real.sqrt_zero] using
      (hc.tendsto 0).comp hε
  have hAP := probability_open_eventual_lower hlim isOpen_ball (half_lt_self hAx)
  have hBP := probability_open_eventual_lower hlim isOpen_ball (half_lt_self hBy)
  apply probability_open_closed_contraction hlim isOpen_ball isClosed_closedBall
    (pow_pos (by norm_num : (0:ℝ)<1/2) n) hcoef
  filter_upwards [hAP,hBP,herror.eventually (Iio_mem_nhds hκ),
    hε.eventually (Iio_mem_nhds (show (0:ℝ)<(ρ-(‖x‖+a))/2 by linarith)),
    hε.eventually (Iio_mem_nhds (show (0:ℝ)<(ρ-(‖y‖+b))/2 by linarith)),
    hε.eventually (Iio_mem_nhds (show (0:ℝ)<S-(ρ+2*η) by linarith))]
    with k hkA hkB hkerr hkx hky hkroom
  have hAcl : 0 < (P k : Measure (Euclidean n)).real (closedBall x a) :=
    (half_pos hAx).trans_le (hkA.trans (measureReal_mono ball_subset_closedBall
      (measure_ne_top _ _)))
  have hBcl : 0 < (P k : Measure (Euclidean n)).real (closedBall y b) :=
    (half_pos hBy).trans_le (hkB.trans (measureReal_mono ball_subset_closedBall
      (measure_ne_top _ _)))
  have hA0 := normalizedBallPushforward_preimage_ne_zero _ (p k) (r k) S (V k)
    (hfin k) (hpos k) (hVm k) measurableSet_closedBall hAcl
  have hB0 := normalizedBallPushforward_preimage_ne_zero _ (p k) (r k) S (V k)
    (hfin k) (hpos k) (hVm k) measurableSet_closedBall hBcl
  have he0 : 0 ≤ ε k := dist_nonneg.trans (hV k).1
  have hm := hX.metric_local_midpoint_law hn (hr k) hS hρ hρS he0
    (by linarith) (V k) (hVm k) (hV k) x y z hx hy (by linarith) (by linarith)
      hA0 hB0 (hfin k)
  dsimp only at hm
  have hs : (closedBall ((1/2:ℝ) • (x+y)) ((a+b)/2+Real.sqrt (2*(ε k*(4*ρ+ε k))))) ⊆
      closedBall ((1/2:ℝ) • (x+y)) ((a+b)/2+κ) :=
    closedBall_subset_closedBall (by linarith)
  have hmono := measureReal_mono hs (measure_ne_top (P k : Measure (Euclidean n)) _)
  have hsource : (midpointFloor K n (2*ρ*r k)).toReal^n*
      (P k : Measure (Euclidean n)).real (ball y b) ≤
      (midpointFloor K n (2*ρ*r k)).toReal^n*
        (P k : Measure (Euclidean n)).real (closedBall y b) := mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := (P k : Measure (Euclidean n))) ball_subset_closedBall
      (measure_ne_top _ _)) (pow_nonneg (ENNReal.toReal_nonneg) n)
  exact hsource.trans (hm.trans hmono)

end RegularPointCoordinates

end

end OAI
