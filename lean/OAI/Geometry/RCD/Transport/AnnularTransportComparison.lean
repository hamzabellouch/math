import OAI.Geometry.RCD.Transport.HyperbolicDistortion

namespace OAI

/-! # Annular volume contraction from the actual CD transport inequality

The initial endpoint is a small ball about the pole; the final endpoint
is an annulus. Retaining the radial distortion, rather than its coarse
exponential lower bound, is the step needed for model volume comparison.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem FullCD.annular_contraction
    (μ : Measure X) [SigmaFinite μ] {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : K ≤ 0) (p : X) {r R δ t : ℝ}
    (_hR : 0 < R) (hδ : 0 < δ) (ht : 0 < t) (ht1 : t < 1) :
    tau K n t (R + δ) ^ n * μ (ball p R \ closedBall p r) ≤
      μ (ball p (t * R + (1 + t) * δ) \ closedBall p (t * r - (1 - t) * δ)) := by
  let A := ball p R \ closedBall p r
  let B := ball p (t * R + (1 + t) * δ) \ closedBall p (t * r - (1 - t) * δ)
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hB : MeasurableSet B := measurableSet_ball.diff measurableSet_closedBall
  by_cases hA0 : μ A = 0
  · change tau K n t (R + δ) ^ n * μ A ≤ μ B
    simp only [hA0, mul_zero, zero_le]
  have hAtop : μ A ≠ ∞ := (hfin A (isBounded_ball.subset sdiff_subset)).ne
  have hsmall0 := (hpos p δ hδ).ne'
  have hsmalltop := (hfin (ball p δ) isBounded_ball).ne
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  let T : Time := ⟨t, ht.le, ht1.le⟩
  have hroot := hcd.support_volume_bound μ K n (ball p δ) A B
    measurableSet_ball hA hB hsmall0 hsmalltop hA0 hAtop
    (uniformOn_finiteSecondMoment μ (ball p δ) measurableSet_ball hsmall0 hsmalltop
      p δ (fun _ hx => hx.le))
    (uniformOn_finiteSecondMoment μ A hA hA0 hAtop p R (fun _ hx => hx.1.le))
    n le_rfl hn1 T (tau K n t (R + δ))
    (by
      intro x hx y hy
      apply tau_antitone_distance_nonpos_curvature hK hn1 ht ht1 dist_nonneg
      have hxy := dist_triangle x p y
      rw [dist_comm p y] at hxy
      change dist x p < δ at hx
      have hyR : dist y p < R := hy.1
      linarith only [hxy, hx, hyR])
    (by
      intro γ hγ h₀ h₁
      have hfirst : dist (γ T) (γ 0) = t * dist (γ 0) (γ 1) := by
        rw [hγ]
        change |t - 0| * dist (γ 0) (γ 1) = _
        rw [sub_zero, abs_of_nonneg ht.le]
      have hlast : dist (γ 1) (γ T) = (1 - t) * dist (γ 0) (γ 1) := by
        rw [hγ]
        change |1 - t| * dist (γ 0) (γ 1) = _
        rw [abs_of_nonneg (sub_nonneg.mpr ht1.le)]
      have hstart : dist (γ 0) p < δ := h₀
      have hend : dist (γ 1) p < R := h₁.1
      have hinner : r < dist (γ 1) p := lt_of_not_ge h₁.2
      have hends := dist_triangle (γ 0) p (γ 1)
      rw [dist_comm p (γ 1)] at hends
      have hupper := dist_triangle (γ T) (γ 0) p
      rw [hfirst] at hupper
      have hlower := dist_triangle (γ 1) (γ T) p
      rw [hlast] at hlower
      change dist (γ T) p < t * R + (1 + t) * δ ∧
        ¬ dist (γ T) p ≤ t * r - (1 - t) * δ
      constructor
      · nlinarith only [hupper, hends, hstart, hend, ht, ht1]
      · nlinarith only [hlower, hends, hstart, hinner, ht, ht1])
  have hpow := ENNReal.rpow_le_rpow hroot hn0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hn0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_one, ENNReal.rpow_natCast] at hpow
  exact hpow

theorem FullCD.ball_contraction_with_center_error
    (μ : Measure X) [SigmaFinite μ] {K : ℝ} {n : ℕ} (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (hK : K ≤ 0) (p : X) {R δ t : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (ht : 0 < t) (ht1 : t < 1) :
    tau K n t (R + δ) ^ n * μ (ball p R) ≤
      μ (ball p (t * R + (1 + t) * δ)) := by
  have hinner : t * (-1) - (1 - t) * δ < 0 := by nlinarith
  simpa only [closedBall_eq_empty.mpr (by norm_num : (-1 : ℝ) < 0),
    closedBall_eq_empty.mpr hinner, sdiff_empty] using
    hcd.annular_contraction μ hpos hfin hn hK p (r := -1) hR hδ ht ht1

end RegularPointCoordinates

end OAI
