import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Cutoff
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartRouting
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothBump

namespace OAI

noncomputable section
namespace VelocityDetection.BurstSchedule
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SmoothProfiles

def amplitude (r : ℝ) : ℝ := step (8*r)-step (8*r-7)

def phase (N : ℕ) (r : ℝ) : ℝ := N*(step (8*r-1)-step (8*r-5))

@[fun_prop] theorem contDiff_amplitude : ContDiff ℝ ∞ amplitude := by
  unfold amplitude
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).sub
    (Real.smoothTransition.contDiff.comp (by fun_prop))

@[fun_prop] theorem contDiff_phase (N : ℕ) : ContDiff ℝ ∞ (phase N) := by
  unfold phase
  exact contDiff_const.mul ((Real.smoothTransition.contDiff.comp (by fun_prop)).sub
    (Real.smoothTransition.contDiff.comp (by fun_prop)))

theorem amplitude_bounds (r : ℝ) : amplitude r ∈ Icc (0:ℝ) 1 := by
  have hh := Real.smoothTransition.monotone (show 8*r-7 ≤ 8*r by linarith)
  exact ⟨sub_nonneg.mpr hh,by
    unfold amplitude
    linarith [Real.smoothTransition.nonneg (8*r-7),Real.smoothTransition.le_one (8*r)]⟩

theorem phase_bounds (N : ℕ) (r : ℝ) : phase N r ∈ Icc (0:ℝ) N := by
  have hh := Real.smoothTransition.monotone (show 8*r-5 ≤ 8*r-1 by linarith)
  have hz : 0 ≤ step (8*r-1)-step (8*r-5) := sub_nonneg.mpr hh
  have h1 : step (8*r-1)-step (8*r-5) ≤ 1 := by
    linarith [Real.smoothTransition.nonneg (8*r-5),Real.smoothTransition.le_one (8*r-1)]
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hz,(mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)).trans_eq (mul_one _)⟩

theorem amplitude_before {r : ℝ} (hr : r ≤ 0) : amplitude r = 0 := by
  rw [amplitude, step,Real.smoothTransition.zero_of_nonpos (by linarith : 8*r ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : 8*r-7 ≤ 0),sub_self]

theorem amplitude_after {r : ℝ} (hr : 1 ≤ r) : amplitude r = 0 := by
  rw [amplitude, step,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8*r),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8*r-7),sub_self]

theorem amplitude_middle {r : ℝ} (hr : r ∈ Icc (1/8:ℝ) (7/8)) : amplitude r = 1 := by
  rw [amplitude, step,Real.smoothTransition.one_of_one_le (by linarith [hr.1] : 1 ≤ 8*r),
    Real.smoothTransition.zero_of_nonpos (by linarith [hr.2] : 8*r-7 ≤ 0),sub_zero]

theorem phase_before (N : ℕ) {r : ℝ} (hr : r ≤ 1/8) : phase N r = 0 := by
  rw [phase, step,Real.smoothTransition.zero_of_nonpos (by linarith : 8*r-1 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : 8*r-5 ≤ 0),sub_self,mul_zero]

theorem phase_after (N : ℕ) {r : ℝ} (hr : 3/4 ≤ r) : phase N r = 0 := by
  rw [phase, step,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8*r-1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8*r-5),sub_self,mul_zero]

theorem phase_middle (N : ℕ) {r : ℝ} (hr : r ∈ Icc (1/4:ℝ) (5/8)) : phase N r = N := by
  rw [phase, step,Real.smoothTransition.one_of_one_le (by linarith [hr.1] : 1 ≤ 8*r-1),
    Real.smoothTransition.zero_of_nonpos (by linarith [hr.2] : 8*r-5 ≤ 0),sub_zero,mul_one]

theorem deriv_amplitude (r : ℝ) : deriv amplitude r = 8*(pulse (8*r)-pulse (8*r-7)) := by
  have h₀ := (differentiable_step (8*r)).hasDerivAt.comp r ((hasDerivAt_id r).const_mul 8)
  have h₁ := (differentiable_step (8*r-7)).hasDerivAt.comp r
    (((hasDerivAt_id r).const_mul 8).sub_const 7)
  convert! (h₀.sub h₁).deriv using 1
  simp only [pulse]
  ring

theorem deriv_phase (N : ℕ) (r : ℝ) : deriv (phase N) r =
    N*8*(pulse (8*r-1)-pulse (8*r-5)) := by
  have h₀ := (differentiable_step (8*r-1)).hasDerivAt.comp r
    (((hasDerivAt_id r).const_mul 8).sub_const 1)
  have h₁ := (differentiable_step (8*r-5)).hasDerivAt.comp r
    (((hasDerivAt_id r).const_mul 8).sub_const 5)
  convert! ((h₀.sub h₁).const_mul (N:ℝ)).deriv using 1
  simp only [pulse]
  ring

theorem deriv_amplitude_before {r : ℝ} (hr : r ≤ 0) : deriv amplitude r = 0 := by
  rw [deriv_amplitude,pulse_zero_of_nonpos (by linarith : 8*r ≤ 0),
    pulse_zero_of_nonpos (by linarith : 8*r-7 ≤ 0),sub_self,mul_zero]

theorem deriv_amplitude_after {r : ℝ} (hr : 1 ≤ r) : deriv amplitude r = 0 := by
  rw [deriv_amplitude,pulse_zero_of_one_le (by linarith : 1 ≤ 8*r),
    pulse_zero_of_one_le (by linarith : 1 ≤ 8*r-7),sub_self,mul_zero]

theorem deriv_amplitude_middle {r : ℝ} (hr : r ∈ Icc (1/8:ℝ) (7/8)) :
    deriv amplitude r = 0 := by
  rw [deriv_amplitude,pulse_zero_of_one_le (by linarith [hr.1] : 1 ≤ 8*r),
    pulse_zero_of_nonpos (by linarith [hr.2] : 8*r-7 ≤ 0),sub_self,mul_zero]

theorem deriv_phase_before (N : ℕ) {r : ℝ} (hr : r ≤ 1/8) : deriv (phase N) r = 0 := by
  rw [deriv_phase,pulse_zero_of_nonpos (by linarith : 8*r-1 ≤ 0),
    pulse_zero_of_nonpos (by linarith : 8*r-5 ≤ 0),sub_self,mul_zero]

theorem deriv_phase_after (N : ℕ) {r : ℝ} (hr : 3/4 ≤ r) : deriv (phase N) r = 0 := by
  rw [deriv_phase,pulse_zero_of_one_le (by linarith : 1 ≤ 8*r-1),
    pulse_zero_of_one_le (by linarith : 1 ≤ 8*r-5),sub_self,mul_zero]

theorem source_at_zero (N : ℕ) (r : ℝ) : deriv amplitude r = 0 ∨ phase N r = 0 := by
  by_cases h₁ : r < 1/8
  · exact Or.inr (phase_before N h₁.le)
  by_cases h₂ : 7/8 < r
  · exact Or.inr (phase_after N (by linarith))
  exact Or.inl (deriv_amplitude_middle ⟨le_of_not_gt h₁,le_of_not_gt h₂⟩)

theorem barrier_slope {s : ℝ} (hs : s ∈ Icc (1/3:ℝ) (2/3)) : 1 ≤ Cutoff.stepD s := by
  have h₀ : ¬ s ≤ 0 := by linarith [hs.1]
  have h₁ : s ≤ 1 := by linarith [hs.2]
  simp only [Cutoff.stepD,Cutoff.joinAt,ite_eq_right h₀,ite_eq_left h₁,Cutoff.polynomialD]
  have hq : 2/9 ≤ s*(1-s) := by nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hs.2)]
  have hsq : (2/9:ℝ)^2 ≤ (s*(1-s))^2 := pow_le_pow_left₀ (by norm_num) hq 2
  nlinarith

def error (k : ℕ) : ℝ := (1/16)*(1/2)^k

theorem error_pos (k : ℕ) : 0 < error k := by unfold error; positivity

theorem error_small (k : ℕ) : error k ≤ 1/16 := by
  unfold error
  exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))

theorem error_sum (L : ℕ) : ∑ k ∈ Finset.range L, error k = (1/8)*(1-(1/2)^L) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ,ih,error,pow_succ]; ring

theorem error_sum_le (L : ℕ) : ∑ k ∈ Finset.range L, error k ≤ (1/8:ℝ) := by
  rw [error_sum]
  have hh : (0:ℝ) ≤ (1/2)^L := by positivity
  linarith

end VelocityDetection.BurstSchedule
end

noncomputable section
namespace VelocityDetection.BurstSchedule
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open SmoothProfiles
variable (A : RoutingData) (ν : ℝ)

def lapBound (k : ℕ) : ℝ := 2*(SmoothBump.bound:ℝ)/(ChartRouting.radius A (k+1))^2

def duration (k : ℕ) : ℝ := error k/(3*(1+ν*lapBound A k))

theorem lapBound_pos (k : ℕ) : 0 < lapBound A k := by
  unfold lapBound
  exact div_pos (mul_pos (by norm_num) (by exact_mod_cast SmoothBump.bound_pos))
    (sq_pos_of_pos (ChartRouting.radius_pos A (k+1)))

theorem duration_pos (hν : 0 ≤ ν) (k : ℕ) : 0 < duration A ν k := by
  unfold duration
  exact div_pos (error_pos k) (by nlinarith [lapBound_pos A k])

theorem duration_small (hν : 0 ≤ ν) (k : ℕ) : duration A ν k ≤ 1/48 := by
  have hh : 0 ≤ ν*lapBound A k := mul_nonneg hν (lapBound_pos A k).le
  unfold duration
  apply (div_le_iff₀ (by linarith : 0 < 3*(1+ν*lapBound A k))).mpr
  linarith [error_small k]

theorem duration_error (hν : 0 ≤ ν) (k : ℕ) : ν*lapBound A k ≤ error k/(3*duration A ν k) := by
  have he : error k/(3*duration A ν k) = 1+ν*lapBound A k := by
    unfold duration
    field_simp [ne_of_gt (error_pos k),ne_of_gt (show 0 < 1+ν*lapBound A k by
      nlinarith [lapBound_pos A k])]
  rw [he]
  linarith

def localTime (k : ℕ) (t : ℝ) : ℝ := (t-(k+1))/duration A ν k

def weight (k : ℕ) (t : ℝ) : ℝ := amplitude (localTime A ν k t)

def clock (k : ℕ) (t : ℝ) : ℝ := phase (k+1) (localTime A ν k t)

@[fun_prop] theorem contDiff_localTime (k : ℕ) : ContDiff ℝ ∞ (localTime A ν k) := by
  unfold localTime
  fun_prop

@[fun_prop] theorem contDiff_weight (k : ℕ) : ContDiff ℝ ∞ (weight A ν k) :=
  contDiff_amplitude.comp (contDiff_localTime A ν k)

@[fun_prop] theorem contDiff_clock (k : ℕ) : ContDiff ℝ ∞ (clock A ν k) :=
  (contDiff_phase (k+1)).comp (contDiff_localTime A ν k)

theorem deriv_weight (k : ℕ) (t : ℝ) : deriv (weight A ν k) t =
    deriv amplitude (localTime A ν k t)/duration A ν k := by
  have ht := ((hasDerivAt_id t).sub_const ((k:ℝ)+1)).div_const (duration A ν k)
  have hh := (contDiff_amplitude.differentiable (by simp) (localTime A ν k t)).hasDerivAt.comp t ht
  convert! hh.deriv using 1
  ring

theorem deriv_clock (k : ℕ) (t : ℝ) : deriv (clock A ν k) t =
    deriv (phase (k+1)) (localTime A ν k t)/duration A ν k := by
  have ht := ((hasDerivAt_id t).sub_const ((k:ℝ)+1)).div_const (duration A ν k)
  have hh := ((contDiff_phase (k+1)).differentiable (by simp) (localTime A ν k t)).hasDerivAt.comp t ht
  convert! hh.deriv using 1
  ring

theorem weight_source (k : ℕ) (t : ℝ) : deriv (weight A ν k) t = 0 ∨ clock A ν k t = 0 := by
  rcases source_at_zero (k+1) (localTime A ν k t) with h | h
  · exact Or.inl (by rw [deriv_weight,h,zero_div])
  · exact Or.inr h

def barrier (k : ℕ) (t : ℝ) : ℝ := error k*Cutoff.step ((localTime A ν k t+1)/3)

theorem contDiff_barrier (k : ℕ) : ContDiff ℝ 2 (barrier A ν k) := by
  exact contDiff_const.mul (Cutoff.contDiff_step.comp
    (((contDiff_localTime A ν k).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).add contDiff_const |>.div_const 3))

theorem deriv_barrier (k : ℕ) (t : ℝ) : deriv (barrier A ν k) t =
    error k/(3*duration A ν k)*Cutoff.stepD ((localTime A ν k t+1)/3) := by
  have ht := ((((hasDerivAt_id t).sub_const ((k:ℝ)+1)).div_const (duration A ν k)).add_const 1).div_const 3
  have hh := ((Cutoff.hasDerivAt_step ((localTime A ν k t+1)/3)).comp t ht).const_mul (error k)
  convert! hh.deriv using 1
  ring

theorem barrier_bounds (k : ℕ) (t : ℝ) : barrier A ν k t ∈ Icc (0:ℝ) (error k) := by
  have hh := Cutoff.step_mem_Icc ((localTime A ν k t+1)/3)
  exact ⟨mul_nonneg (error_pos k).le hh.1,(mul_le_mul_of_nonneg_left hh.2 (error_pos k).le).trans_eq (mul_one _)⟩

theorem barrier_deriv_nonneg (hν : 0 ≤ ν) (k : ℕ) (t : ℝ) : 0 ≤ deriv (barrier A ν k) t := by
  rw [deriv_barrier]
  exact mul_nonneg (div_nonneg (error_pos k).le (mul_nonneg (by norm_num) (duration_pos A ν hν k).le))
    (Cutoff.stepD_nonneg _)

theorem barrier_deriv_large (hν : 0 ≤ ν) (k : ℕ) {t : ℝ}
    (ht : localTime A ν k t ∈ Icc (0:ℝ) 1) :
    ν*lapBound A k ≤ deriv (barrier A ν k) t := by
  rw [deriv_barrier]
  have h := barrier_slope (s := (localTime A ν k t+1)/3) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  exact (duration_error A ν hν k).trans (le_mul_of_one_le_right (div_nonneg (error_pos k).le (mul_nonneg (by norm_num) (duration_pos A ν hν k).le)) h)

end VelocityDetection.BurstSchedule
end

end OAI
