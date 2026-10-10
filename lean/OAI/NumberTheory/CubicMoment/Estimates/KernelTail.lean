import OAI.NumberTheory.CubicMoment.Estimates.IntervalSmoothing

namespace OAI

/-!
# Quantitative kernel tails

A finite weighted L¹ moment gives a uniform bound for the two endpoint
tails. Scaling the kernel will make the moment independent of the
truncation height, as required for a sharp cutoff.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def kernelMoment (k : ℝ → ℂ) (T : ℝ) : ℝ :=
  ∫ y, ‖k y‖ * (1 + T * |y|) ^ 2

theorem kernel_tail_le_moment {k : ℝ → ℂ} (hk : Integrable k)
    {T d : ℝ} (hT : 0 ≤ T) (hd : 0 ≤ d)
    (hM : Integrable (fun y => ‖k y‖ * (1 + T * |y|) ^ 2)) :
    (∫ y, if d ≤ |y| then ‖k y‖ else 0) ≤ kernelMoment k T / (1 + T*d)^2 := by
  have hden : 0 < (1 + T*d)^2 := sq_pos_of_pos (by positivity)
  rw [kernelMoment, ← integral_div]
  apply integral_mono
    (hk.norm.indicator (measurableSet_le measurable_const measurable_id.abs))
    (hM.div_const _)
  intro y
  change (if d ≤ |y| then ‖k y‖ else 0) ≤ (‖k y‖ * (1 + T*|y|)^2) / (1 + T*d)^2
  by_cases hy : d ≤ |y|
  · simp only [hy, ite_true]
    apply (le_div_iff₀ hden).mpr
    have hh : (1 + T*d)^2 ≤ (1 + T*|y|)^2 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    exact mul_le_mul_of_nonneg_left hh (_root_.norm_nonneg (k y))
  · simp only [hy, ite_false]
    positivity

/-- A moment bound proves the error estimate; it is not assumed as an
unproved boundary approximation. -/
theorem intervalSmoothing_error_le_moment {k : ℝ → ℂ} (hk : Integrable k)
    (hmass : ∫ y, k y = 1) {T : ℝ} (hT : 0 ≤ T)
    (hM : Integrable (fun y => ‖k y‖ * (1 + T * |y|) ^ 2)) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing k a b s‖ ≤
      kernelMoment k T / (1 + T*|s-a|)^2 +
        kernelMoment k T / (1 + T*|s-b|)^2 :=
  (intervalSmoothing_error_le_tails hk hmass a b s).trans
    (add_le_add (kernel_tail_le_moment hk hT (abs_nonneg _) hM)
      (kernel_tail_le_moment hk hT (abs_nonneg _) hM))

end CubicFirstMoment

end

end OAI
