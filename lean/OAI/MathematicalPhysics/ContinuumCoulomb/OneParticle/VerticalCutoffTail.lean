import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCappedForm

namespace OAI

/-! Gaussian control of the inner-slab projection error for the actual
transverse cutoff. The loss decays exponentially in the square of the slab
width, with the oscillator frequency fixed by the construction. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalCutoffError (freq S z : ℝ) : ℝ :=
  (verticalInnerCutoff S z-1)*verticalMode freq z

theorem verticalCutoffError_memLp {freq : ℝ} (hfreq : 0 < freq) (S : ℝ) :
    MemLp (verticalCutoffError freq S) 2 := by
  apply (verticalMode_memLp hfreq).of_le_mul (c := 2)
    ((((verticalInnerCutoff_smooth S).continuous.sub continuous_const).mul
      (verticalMode_smooth freq).continuous).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖(verticalInnerCutoff S z-1)*verticalMode freq z‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h := abs_sub (verticalInnerCutoff S z) (1:ℝ)
  have hs := Real.abs_sin_le_one (verticalCutoffAngle S z)
  simp only [abs_one] at h
  change |verticalInnerCutoff S z| ≤ 1 at hs
  linarith

def verticalCutoffTailConstant (freq : ℝ) : ℝ :=
  (4 / Real.sqrt (Real.pi/freq)) * ∫ z : ℝ, Real.exp (-(freq/2)*z^2)

theorem verticalCutoffTailConstant_nonnegative (freq : ℝ) :
    0 ≤ verticalCutoffTailConstant freq := by
  unfold verticalCutoffTailConstant
  exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (integral_nonneg (fun z => (Real.exp_pos _).le))

theorem verticalCutoffError_square_bound {freq S : ℝ}
    (hfreq : 0 < freq) (hS : 0 < S) (z : ℝ) :
    verticalCutoffError freq S z^2 ≤
      ((4 / Real.sqrt (Real.pi/freq)) * Real.exp (-freq*S^2/8)) *
        Real.exp (-(freq/2)*z^2) := by
  by_cases hz : |z| ≤ S/2
  · rw [verticalCutoffError, (verticalCutoff_inner hS hz).1, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hz' : S/2 ≤ |z| := (le_of_not_ge hz)
    have hsq : S^2/4 ≤ z^2 := by
      have h := (sq_le_sq₀ (by positivity : 0 ≤ S/2) (abs_nonneg z)).mpr hz'
      nlinarith [sq_abs z]
    have hd : (verticalInnerCutoff S z-1)^2 ≤ (4:ℝ) := by
      have h := abs_sub (verticalInnerCutoff S z) (1:ℝ)
      have hs := Real.abs_sin_le_one (verticalCutoffAngle S z)
      simp only [abs_one] at h
      change |verticalInnerCutoff S z| ≤ 1 at hs
      have ha : |verticalInnerCutoff S z-1| ≤ 2 := by linarith
      nlinarith [sq_abs (verticalInnerCutoff S z-1), abs_nonneg (verticalInnerCutoff S z-1)]
    have he : Real.exp (-freq*z^2) ≤
        Real.exp (-freq*S^2/8)*Real.exp (-(freq/2)*z^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hfreq.le]
    unfold verticalCutoffError
    rw [mul_pow, verticalMode_square hfreq]
    calc
      _ ≤ 4 * (Real.exp (-freq*z^2) / Real.sqrt (Real.pi/freq)) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ 4 * ((Real.exp (-freq*S^2/8)*Real.exp (-(freq/2)*z^2)) /
          Real.sqrt (Real.pi/freq)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)) (by norm_num)
      _ = _ := by ring

theorem verticalCutoffError_integral_bound {freq S : ℝ}
    (hfreq : 0 < freq) (hS : 0 < S) :
    (∫ z, verticalCutoffError freq S z^2) ≤
      verticalCutoffTailConstant freq * Real.exp (-freq*S^2/8) := by
  have hi : Integrable (fun z => verticalCutoffError freq S z^2) :=
    (memLp_two_iff_integrable_sq (verticalCutoffError_memLp hfreq S).aestronglyMeasurable).mp
      (verticalCutoffError_memLp hfreq S)
  have he := (integrable_exp_neg_mul_sq (show 0 < freq/2 by linarith)).const_mul
    ((4 / Real.sqrt (Real.pi/freq)) * Real.exp (-freq*S^2/8))
  have h := integral_mono hi he (verticalCutoffError_square_bound hfreq hS)
  rw [integral_const_mul] at h
  convert h using 1
  unfold verticalCutoffTailConstant
  ring

/-- The projection error is bounded for every actual L2 test function. -/
theorem verticalCutoff_pair_error {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (u : ℝ → ℝ) (hu : MemLp u 2) :
    ((∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z) -
      (∫ z, u z*verticalMode freq z))^2 ≤
      (∫ z, u z^2)*(verticalCutoffTailConstant freq * Real.exp (-freq*S^2/8)) := by
  have hi₀ : Integrable (fun z => u z*verticalMode freq z) := hu.integrable_mul (verticalMode_memLp hfreq)
  have hi₁ : Integrable (fun z => u z*verticalCutoffError freq S z) :=
    hu.integrable_mul (verticalCutoffError_memLp hfreq S)
  have hp : (∫ z, (verticalInnerCutoff S z*u z)*verticalMode freq z) -
      (∫ z, u z*verticalMode freq z) = ∫ z, u z*verticalCutoffError freq S z := by
    have he : (fun z => (verticalInnerCutoff S z*u z)*verticalMode freq z) =
        (fun z => u z*verticalMode freq z + u z*verticalCutoffError freq S z) := by
      funext z
      unfold verticalCutoffError
      ring
    rw [he, integral_add hi₀ hi₁]
    ring
  rw [hp]
  have hpair (f g : ℝ → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ z, f z*g z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hz hf'
    rw [hz, hf', RCLike.inner_apply, conj_trivial]
    ring
  have h := real_inner_mul_inner_self_le (hu.toLp u)
    ((verticalCutoffError_memLp hfreq S).toLp (verticalCutoffError freq S))
  rw [hpair _ _ hu (verticalCutoffError_memLp hfreq S), hpair _ _ hu hu,
    hpair _ _ (verticalCutoffError_memLp hfreq S) (verticalCutoffError_memLp hfreq S)] at h
  have hc := verticalCutoffError_integral_bound hfreq hS
  simp only [← pow_two] at h
  exact h.trans (mul_le_mul_of_nonneg_left hc (integral_nonneg (fun z => sq_nonneg _)))

end ContinuumCoulomb

end

end OAI
