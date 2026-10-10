import OAI.Geometry.RCD.Metric.ModelVolumeComparison

namespace OAI

/-! # The five-ball volume bound used by the local maximal estimate -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem model_five_ball_bound (μ : Measure X) {n : ℕ} (hn : 0 < n)
    {a R : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison μ (comparisonModelVolume (n-1) a))
    (p : X) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    μ.real (ball p (5*r)) ≤
      (Real.cosh (a*(5*R))^(n-1)*5^n)*μ.real (ball p r) := by
  have hR : 0 < R := hr.trans_le hrR
  have hn' : n-1+1=n := by omega
  have hlo := (comparisonModelVolume_bounds (n-1) ha hr.le).1
  have hhi := (comparisonModelVolume_bounds (n-1) ha
    (by positivity : 0 ≤ 5*r)).2
  rw [hn'] at hlo hhi
  have hc : Real.cosh (a*(5*r)) ≤ Real.cosh (a*(5*R)) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) ha
  have hhi' : comparisonModelVolume (n-1) a (5*r) ≤
      Real.cosh (a*(5*R))^(n-1)*(5*r)^n :=
    hhi.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.cosh_pos _).le hc _) (by positivity))
  have hb := hBG p r (5*r) hr (by linarith)
  have hh : μ.real (ball p (5*r))*r^n ≤
      ((Real.cosh (a*(5*R))^(n-1)*5^n)*μ.real (ball p r))*r^n := by
    calc
      _ ≤ μ.real (ball p (5*r))*comparisonModelVolume (n-1) a r :=
        mul_le_mul_of_nonneg_left hlo measureReal_nonneg
      _ ≤ μ.real (ball p r)*comparisonModelVolume (n-1) a (5*r) := hb
      _ ≤ μ.real (ball p r)*(Real.cosh (a*(5*R))^(n-1)*(5*r)^n) :=
        mul_le_mul_of_nonneg_left hhi' measureReal_nonneg
      _ = _ := by rw [mul_pow]; ring
  exact (mul_le_mul_iff_left₀ (pow_pos hr n)).mp hh

end RegularPointCoordinates

end

end OAI
