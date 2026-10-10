import OAI.Geometry.RCD.Metric.NearbySmallBallMass

namespace OAI

/-! # A sufficiently small omitted mass leaves a good point near the center -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.good_set_inner_point {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {R ζ : ℝ} (hR : 0 < R)
    (hζ : 0 ≤ ζ) (hsmall : ζ*((Real.cosh 1^(n-1)*2^n)*(16*16384)^n) < 1)
    (hcurv : -1 ≤ K*(32*R)^2) {U : Set X}
    (hbad : (hausdorff n X).real (ball p R \ U) ≤
      ζ*(hausdorff n X).real (ball p (16*R))) :
    ∃ z ∈ U, dist z p < R/16384 := by
  let μ := hausdorff n X
  let G := (Real.cosh 1^(n-1)*2^n)*(16*16384)^n
  have hpos : 0 < μ.real (ball p (R/16384)) := ENNReal.toReal_pos
    (hX.fullSupport p _ (by positivity)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hv := hX.nearby_small_ball_mass hn (p := p) (z := p) (R := 16*R) (r := R/16384)
    (by positivity) (by simp only [dist_self]; positivity) (by positivity)
    (by linarith only [hR]) (by convert hcurv using 1; ring)
  have hratio : μ.real (ball p (16*R)) ≤ G*μ.real (ball p (R/16384)) := by
    have hscale : μ.real (ball p (16*R))*R^n ≤
        (G*μ.real (ball p (R/16384)))*R^n := by
      calc
        _ = (μ.real (ball p (16*R))*(R/16384)^n)*(16384:ℝ)^n := by
          rw [div_pow]
          field_simp
        _ ≤ ((Real.cosh 1^(n-1)*2^n)*(16*R)^n*
            μ.real (ball p (R/16384)))*(16384:ℝ)^n :=
          mul_le_mul_of_nonneg_right hv (by positivity)
        _ = _ := by dsimp only [G]; simp only [mul_pow]; ring
    exact (mul_le_mul_iff_left₀ (pow_pos hR n)).mp hscale
  have hstrict : μ.real (ball p R \ U) < μ.real (ball p (R/16384)) := by
    apply (hbad.trans (mul_le_mul_of_nonneg_left hratio hζ)).trans_lt
    have hh := mul_lt_mul_of_pos_right hsmall hpos
    dsimp only [G] at *
    nlinarith only [hh]
  by_contra hnot
  push Not at hnot
  have hsub : ball p (R/16384) ⊆ ball p R \ U := by
    intro z hz
    refine ⟨ball_subset_ball (by linarith only [hR]) hz,?_⟩
    intro hzU
    exact not_lt_of_ge (hnot z hzU) hz
  have hm := measureReal_mono (μ := μ) hsub
    (measure_ne_top_of_subset sdiff_subset (hX.finiteOnBounded _ isBounded_ball).ne)
  exact (not_lt_of_ge hm) hstrict

end RegularPointCoordinates

end

end OAI
