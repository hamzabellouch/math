import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetectorCutoff

namespace OAI

/-! The concrete detector has a uniformly bounded radial derivative.
This supplies the actual variation cost when one prime is left free in
the stopped coefficient; it is not a sequence-cancellation assumption. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma primeDetectorCutoff_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv primeDetectorCutoff x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn primeDetectorCutoff (fun _ : ℝ => (1:ℝ)) (Iio 1) :=
      fun y hy => primeDetectorCutoff_one hy.le
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      have h := not_and_or.mp hx
      rcases h with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn primeDetectorCutoff (fun _ : ℝ => (0:ℝ)) (Ioi 2) :=
      fun y hy => primeDetectorCutoff_zero hy.le
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem primeDetectorCutoff_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D := by
  have hd : Continuous (deriv primeDetectorCutoff) :=
    primeDetectorCutoff_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv primeDetectorCutoff x‖*x‖ ≤ D at h
    have hn : 0 ≤ ‖deriv primeDetectorCutoff x‖*x := mul_nonneg (_root_.norm_nonneg _) hx.le
    rw [Real.norm_eq_abs,abs_of_nonneg hn] at h
    simpa only [Real.norm_eq_abs] using h.trans (le_max_left D 0)
  · rw [primeDetectorCutoff_deriv_zero hmem,abs_zero,zero_mul]
    exact le_max_right _ _

end CubicFirstMoment

end

end OAI
