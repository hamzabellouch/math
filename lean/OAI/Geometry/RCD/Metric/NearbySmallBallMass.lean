import OAI.Geometry.RCD.Metric.ModelScaleControl

namespace OAI

/-! # Relative lower volume for the source balls of the hole cover

The denominator is the mass of one fixed surrounding ball. No absolute
Euclidean density or volume-convergence input is used.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.nearby_small_ball_mass {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p z : X} {R r : ℝ}
    (hR : 0 < R) (hz : dist z p ≤ R) (hr : 0 < r) (hrR : r ≤ R)
    (hcurv : -1 ≤ K*(2*R)^2) :
    (hausdorff n X).real (ball p R)*r^n ≤
      (Real.cosh 1^(n-1)*2^n)*R^n*(hausdorff n X).real (ball z r) := by
  let μ := hausdorff n X
  obtain ⟨a,ha,hBG,hscale⟩ := hX.model_comparison_with_scale_control hn
  have haR : a*(2*R) ≤ 1 := by
    have hh := hscale (2*R/3) (by positivity) (by nlinarith [hcurv])
    simpa only [show 3*(2*R/3)=2*R by ring] using hh
  have hsub : ball p R ⊆ ball z (2*R) := by
    intro x hx
    have hh := dist_triangle x p z
    rw [dist_comm p z] at hh
    have hxp : dist x p < R := hx
    change dist x z < 2*R
    linarith
  have hmass : μ.real (ball p R) ≤ μ.real (ball z (2*R)) :=
    measureReal_mono hsub (hX.finiteOnBounded _ isBounded_ball).ne
  have hn' : n-1+1=n := by omega
  have hlo := (comparisonModelVolume_bounds (n-1) ha hr.le).1
  have hhi := (comparisonModelVolume_bounds (n-1) ha
    (by positivity : 0 ≤ 2*R)).2
  rw [hn'] at hlo hhi
  have hc : Real.cosh (a*(2*R)) ≤ Real.cosh 1 := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity),abs_one]
    exact haR
  have hhi' : comparisonModelVolume (n-1) a (2*R) ≤ Real.cosh 1^(n-1)*(2*R)^n :=
    hhi.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.cosh_pos _).le hc _) (by positivity))
  calc
    _ ≤ μ.real (ball z (2*R))*comparisonModelVolume (n-1) a r :=
      mul_le_mul hmass hlo (pow_nonneg hr.le _) measureReal_nonneg
    _ ≤ μ.real (ball z r)*comparisonModelVolume (n-1) a (2*R) :=
      hBG z r (2*R) hr (by linarith)
    _ ≤ μ.real (ball z r)*(Real.cosh 1^(n-1)*(2*R)^n) :=
      mul_le_mul_of_nonneg_left hhi' measureReal_nonneg
    _ = _ := by rw [mul_pow]; ring

end RegularPointCoordinates

end

end OAI
