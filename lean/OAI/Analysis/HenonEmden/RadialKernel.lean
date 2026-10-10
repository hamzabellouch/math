import OAI.Analysis.HenonEmden.KernelBalls

namespace OAI

section RadialKernel

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE

lemma source_near_radial_bound {n : ℕ} {v : Space n → ℝ} (hv : Continuous v)
    (hvp : ∀ x, 0 < v x) {p : ℝ} (hp : 0 < p) (A : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Space n, 0 < ‖x‖ → ‖x‖ ≤ 2 →
      ∀ y : Space n, ‖x-y‖ < ‖x‖/2 → source v p A y ≤ M*‖x‖^A := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Space n) 3).exists_bound_of_continuousOn hv.continuousOn
  let C' := max C 1
  refine ⟨C'^p*(2:ℝ)^|A|,by positivity,?_⟩
  intro x hx hx2 y hy
  have hnorm : ‖y‖ ≤ ‖x‖+‖x-y‖ := by
    simpa only [show x+(y-x)=y by abel,norm_sub_rev x y] using norm_add_le x (y-x)
  have hnorm' : ‖x‖ ≤ ‖y‖+‖x-y‖ := by
    simpa only [show y+(x-y)=x by abel] using norm_add_le y (x-y)
  have hy0 : 0 < ‖y‖ := by linarith
  have hy3 : y ∈ closedBall (0:Space n) 3 := mem_closedBall_zero_iff.mpr (by linarith)
  have hvC : v y ≤ C' := (le_abs_self _).trans ((hC y hy3).trans (le_max_left _ _))
  have hvpow : (v y)^p ≤ C'^p := Real.rpow_le_rpow (hvp y).le hvC hp.le
  rw [source_off_zero v p A (norm_ne_zero_iff.mp hy0.ne')]
  have hweight := WeakPDE.rpow_half_double_bound hx (by linarith : ‖x‖/2 ≤ ‖y‖) (by linarith : ‖y‖ ≤ 2*‖x‖) A
  exact (mul_le_mul hweight hvpow (Real.rpow_nonneg (hvp y).le p) (by positivity)).trans_eq (by ring)

lemma radial_kernel_far_bound {n : ℕ} {x y : Space n} (hx : 0 < ‖x‖)
    (hy : ‖x‖/2 ≤ ‖x-y‖) :
    |kernelDir x (x-y)| ≤ 2*|2-(n:ℝ)| *‖x-y‖^(2-(n:ℝ)) := by
  have hs : 0 < ‖x-y‖ := lt_of_lt_of_le (half_pos hx) hy
  have he : ‖x-y‖^(1-(n:ℝ)) = ‖x-y‖^(2-(n:ℝ))/‖x-y‖ := by
    calc
      _ = ‖x-y‖^(2-(n:ℝ)-1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_sub hs,Real.rpow_one]
  have hb := kernelDir_bound x (x-y)
  simp only [finrank_euclideanSpace_fin] at hb
  rw [he] at hb
  refine hb.trans ?_
  have hr : ‖x‖/‖x-y‖ ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  calc
    _ = (‖x‖/‖x-y‖)*(|2-(n:ℝ)| *‖x-y‖^(2-(n:ℝ))) := by ring
    _ ≤ 2*(|2-(n:ℝ)| *‖x-y‖^(2-(n:ℝ))) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by ring

end HenonLaneEmden
end
end RadialKernel

end OAI
