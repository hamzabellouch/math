import OAI.Geometry.Convex.GeneralMahler.CDF

namespace OAI
/-! Explicit exponential tail and ball estimates for standard Gaussian.
Constants depend only on the ambient dimension (and polynomial degree). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
variable {m : ℕ}

theorem normal_tail (m n : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ s : ℝ, 0 ≤ s →
    (∫ x : Rn m in {x | s ≤ ‖x‖}, (1+‖x‖)^n ∂(normal m)) ≤ C * exp (-(s ^ 2)/4) := by
  classical
  let c := (√(2 * π))⁻¹ ^ m
  let f := fun x : Rn m => (1+‖x‖)^n * Real.exp (-(1 * ‖x‖))
  have hi : Integrable f := integrable_polynomial_exp_tail zero_lt_one _
  use (c * exp 1)*(∫ x, f x)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨mul_nonneg (by positivity) (integral_nonneg fun x => by dsimp [f]; positivity),?_⟩
  intro s hs
  let S := {x : Rn m|s ≤ ‖x‖}
  have hm : MeasurableSet S :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  let g := fun x : Rn m => (1+‖x‖)^n
  change ∫ x in S, g x ∂normal m ≤ _
  rw [← integral_indicator hm,normal_integral]
  let a := c * exp 1 * exp (-(s^2)/4)
  have HE (x) : nDensity x • S.indicator g x ≤ a*f x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      change c*_ * g x ≤ _
      have h1 : exp (-(‖x‖^2)/2) ≤ exp 1 * exp (-(s^2)/4) * exp (-(1*‖x‖)) := by
        change s ≤ ‖x‖ at hx
        rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (‖x‖-2)]
      have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc)
        (show 0 ≤ g x by dsimp [g]; positivity)
      dsimp only [g,a,f] at *
      linarith
    · rw [indicator_of_notMem hx,smul_zero]
      dsimp [a,f]; positivity
  have hu := (integrable_envelope (μ := normal m) n).indicator hm
  calc
    _ ≤ ∫ x, a*f x := integral_mono (normal_integrable_iff.mp hu) (hi.const_mul _) HE
    _ = _ := by rw [integral_const_mul]; dsimp [a]; ring

/-- Uniform lower estimate for the Gaussian mass of a ball measured in
standard coordinates. -/
theorem normal_ball_lower (m : ℕ) {r:ℝ} (hr : 0 < r) :
    ∃ c > (0:ℝ), ∀ (x:Rn m),
      c * exp (-((‖x‖+r)^2)/2) ≤ (normal m).real (closedBall x r) := by
  classical
  let c := (√(2 * π))⁻¹ ^ m
  let v := volume.real (closedBall (0:Rn m) r)
  have hp : 0 < v := ENNReal.toReal_pos (measure_closedBall_pos _ _ hr).ne'
    measure_closedBall_lt_top.ne
  have hc : 0 < c := by dsimp [c]; positivity
  use v*c
  refine ⟨by positivity,?_⟩
  intro x
  let S := closedBall x r
  have hm : MeasurableSet S := measurableSet_closedBall
  let a := c*exp (-((‖x‖+r)^2)/2)
  have HE (t:Rn m) (ht : t ∈ S) : a ≤ nDensity t := by
    change c*_ ≤ c*_
    have h1 : ‖t‖ ≤ ‖x‖+r := by
      rw [show ‖x‖ + r = r + ‖x‖ by ring]
      apply le_trans (show ‖t‖ ≤ ‖t-x‖ + ‖x‖ by simpa using norm_add_le (t-x) x)
      gcongr
      change dist t x ≤ r at ht; simpa [dist_eq_norm] using ht
    gcongr
  change _ ≤ (normal m).real S
  rw [← integral_indicator_one hm,normal_integral]
  have hi : Integrable (S.indicator (1 : Rn m → ℝ)) (normal m) :=
    (integrable_const _).indicator hm
  have hu : Integrable (S.indicator fun _ : Rn m => a) := by
    apply (integrable_indicator_iff hm).mpr
    exact integrableOn_const (hs := measure_closedBall_lt_top.ne)
  have hv : (∫ t, S.indicator (fun _ : Rn m => a) t) = v*a := by
    rw [integral_indicator hm, setIntegral_const]
    change volume.real _ * a = _
    have hb : volume.real S = v := by
      change (volume (closedBall x r)).toReal = (volume (closedBall 0 r) : ℝ≥0∞).toReal
      rw [Measure.addHaar_closedBall_center]
    rw [hb]
  rw [mul_assoc]
  change v*a ≤ _
  rw [← hv]
  apply integral_mono hu (normal_integrable_iff.mp hi)
  intro t
  by_cases ht : t ∈ S
  · simpa [indicator_of_mem ht] using HE t ht
  · simp [indicator_of_notMem ht]

/-- Useful for absorbing large cutoff estimates into the smaller Gaussian
lower bound in Lemma Gaussian layer tails. -/
lemma tail_exp_le_a (s : ℝ) (hs : 0 ≤ s) :
    Real.exp (-( (4*(1+s))^2) / 4) ≤ (√(2*π)) * Real.exp 4 * Layers.a (-s) := by
  have h := Layers.a_low s hs
  rw [phi_apply] at h
  have hsq : 0 < √(2*π) := by positivity
  have hE : 1+s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have h₁ : Real.exp (-((4*(1+s))^2)/4) * (1+s)^2 ≤ Real.exp (-(s^2)/2) := calc
    _ ≤ Real.exp (-((4*(1+s))^2)/4) * (Real.exp s * Real.exp s) := by rw [← pow_two]; gcongr
    _ ≤ _ := by
      simp_rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have h₂ := mul_le_mul_of_nonneg_left h (show 0 ≤ √(2*π)*Real.exp 4 by positivity)
  apply le_trans _ h₂
  calc
    _ ≤ Real.exp (-(s^2)/2) / (1+s)^2 := (le_div_iff₀ (by positivity)).mpr h₁
    _ = _ := by rw [Real.exp_neg (4:ℝ)]; field_simp

end GeneralMahler

end

end OAI
