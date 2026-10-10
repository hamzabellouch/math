import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Expanding interior balls and their volume factors -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- Expanding radii have a dyadic gap available for a local mean estimate. -/
theorem expanding_radii {R : ℝ} (hR : 0 < R) (i : ℕ) :
    0 < R/(4*2^i) ∧ R/(4*2^i) ≤ R ∧
    0 < R-R/(2*2^i) ∧ R-R/(2*2^i) < R ∧
    (R-R/(2*2^i))+R/(4*2^i) = R-R/(2*2^(i+1)) := by
  have hp : (0:ℝ) < 2^i := by positivity
  have h1 : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
  have hh : R/(2*2^i) ≤ R/2 :=
    div_le_div_of_nonneg_left hR.le (by norm_num) (by nlinarith)
  refine ⟨by positivity,?_,by linarith,by have := div_pos hR (by positivity : 0 < 2*(2:ℝ)^i); linarith,?_⟩
  · have := div_le_div_of_nonneg_left hR.le (by norm_num : (0:ℝ)<1)
      (by nlinarith : (1:ℝ) ≤ 4*2^i)
    simpa using this
  · rw [pow_succ]
    field_simp
    ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The reciprocal volume cost grows by a fixed geometric factor. -/
theorem NoncollapsedRCD.expanding_volume_factor {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) (R : ℝ)
    (hR : 0 < R) (hcurv : -1 ≤ K*R^2) (i : ℕ) (q : X) (hq : dist q p ≤ R) :
    (hausdorff n X).real (ball p R) ≤
      ((8*Real.exp 4)^n*(2^n:ℝ)^i)*(hausdorff n X).real (ball q (R/(4*2^i))) := by
  let δ : ℝ := 1/(4*2^i)
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hh : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
    nlinarith
  have hv := hX.rescaled_ball_volume_lower hn (by norm_num : (0:ℝ) ≤ 1)
    hδ hδ1 p R hR hcurv q hq
  have he : δ*R = R/(4*2^i) := by dsimp only [δ]; ring
  have hc : (δ/(2*Real.exp (4*Real.sqrt 1)))^n *
      ((8*Real.exp 4)^n*(2^n:ℝ)^i) = 1 := by
    rw [Real.sqrt_one]
    have hh : (2^n:ℝ)^i = (2^i:ℝ)^n := pow_right_comm 2 n i
    rw [hh,← mul_pow,← mul_pow]
    have hbase : δ/(2*Real.exp 4)*(8*Real.exp 4)*(2^i) = 1 := by
      dsimp only [δ]
      field_simp
      ring
    simpa only [mul_one,mul_assoc,one_pow] using congrArg (fun x : ℝ => x^n) hbase
  have hm := mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ (8*Real.exp 4)^n*(2^n:ℝ)^i)
  rw [he] at hm
  calc
    _ = (((8*Real.exp 4)^n*(2^n:ℝ)^i)*(δ/(2*Real.exp (4*Real.sqrt 1)))^n)*
        (hausdorff n X).real (ball p R) := by rw [mul_comm _ ((δ/_)^n),hc,one_mul]
    _ ≤ _ := by simpa only [mul_assoc] using hm

end RegularPointCoordinates

end

end OAI
