import OAI.Analysis.HenonEmden.RadialKernel

namespace OAI

section RadialGradient

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE

lemma IsSolution.radial_kernel_absolute_bounded {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, x ≠ 0 → ‖x‖ ≤ 2 →
      (∫ y, |kernelDir x (x-y)*source v p A y|) ≤ C := by
  have hn3 := h.dimension_ge_three hn
  have hd := (newtonDenom_pos hn3).le
  have hn1 : 1 ≤ Module.finrank ℝ (Space n) := by simp; omega
  have hA := h.first_weight_gt_neg_two hn
  obtain ⟨M,hM,hnear⟩ := source_near_radial_bound h.continuous_v h.positive_v hp A
  obtain ⟨U,hU⟩ := (isCompact_closedBall (0:Space n) 2).exists_bound_of_continuousOn h.continuous_u.continuousOn
  let J : ℝ := ∫ z : Space n in ball 0 1, ‖z‖^(1-(n:ℝ))
  have hJ : 0 ≤ J := integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  let C : ℝ := |2-(n:ℝ)| *M*2^(A+2)*J+2*|2-(n:ℝ)| *newtonDenom n*max U 0
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x hx hx2
  have hr := norm_pos_iff.mpr hx
  let H : Space n → ℝ := (ball x (‖x‖/2)).indicator (fun y => ‖x-y‖^(1-(n:ℝ)))
  have hiH : Integrable H := integrable_shifted_power_ball hn1 (by simp only [finrank_euclideanSpace_fin]; linarith) _ _
  have hH (y : Space n) : 0 ≤ H y := indicator_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) y
  have hS (y : Space n) := source_nonneg (fun y => (h.positive_v y).le) p A y
  have hdom (y : Space n) : |kernelDir x (x-y)*source v p A y| ≤
      (|2-(n:ℝ)| *‖x‖*(M*‖x‖^A))*H y+
      (2*|2-(n:ℝ)|)*(‖x-y‖^(2-(n:ℝ))*source v p A y) := by
    rw [abs_mul,abs_of_nonneg (hS y)]
    by_cases hy : ‖x-y‖ < ‖x‖/2
    · have hy' : y ∈ ball x (‖x‖/2) := by simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hy
      have hk := kernelDir_bound x (x-y)
      simp only [finrank_euclideanSpace_fin] at hk
      have hh := mul_le_mul hk (hnear x hr hx2 y hy) (hS y) (by positivity)
      rw [show H y=‖x-y‖^(1-(n:ℝ)) from indicator_of_mem hy' _]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2*|2-(n:ℝ)|) (mul_nonneg (Real.rpow_nonneg (norm_nonneg (x-y)) (2-(n:ℝ))) (hS y))]
    · have hk := mul_le_mul_of_nonneg_right (radial_kernel_far_bound hr (le_of_not_gt hy)) (hS y)
      have hzero : H y=0 := indicator_of_notMem (by simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hy) _
      rw [hzero,mul_zero,zero_add]
      simpa only [mul_assoc] using hk
  have hi := (h.gradient_u hn hq hx x).1.norm
  simp only [Real.norm_eq_abs] at hi
  have hh := integral_mono hi ((hiH.const_mul _).add ((h.kernel_g_integrable hn x).const_mul _)) hdom
  simp only [Pi.add_apply] at hh
  rw [integral_add (hiH.const_mul _) ((h.kernel_g_integrable hn x).const_mul _),integral_const_mul,integral_const_mul] at hh
  have heH : (∫ y, H y) = ‖x‖/2*J := by
    simpa only [finrank_euclideanSpace_fin,show (n:ℝ)+(1-(n:ℝ))=1 by ring,Real.rpow_one] using
      integral_shifted_power_ball (1-(n:ℝ)) (half_pos hr) x
  have heP : (∫ y, ‖x-y‖^(2-(n:ℝ))*source v p A y) = newtonDenom n*u x := by
    simpa only [rawPotential,finrank_euclideanSpace_fin] using (h.potential_u hn hq hx).symm
  rw [heH,heP] at hh
  have hpower : ‖x‖*‖x‖^A*‖x‖ = ‖x‖^(A+2) := by
    rw [show A+2=A+1+1 by ring,Real.rpow_add hr,Real.rpow_add hr,Real.rpow_one]
    ring
  have hpowle : ‖x‖^(A+2) ≤ (2:ℝ)^(A+2) := Real.rpow_le_rpow hr.le hx2 (by linarith)
  have huU : u x ≤ max U 0 := (le_abs_self _).trans ((hU x (mem_closedBall_zero_iff.mpr hx2)).trans (le_max_left _ _))
  have hbound1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowle (mul_nonneg (abs_nonneg (2-(n:ℝ))) hM)) hJ
  have hbound2 := mul_le_mul_of_nonneg_left huU (by positivity : 0 ≤ 2*|2-(n:ℝ)| *newtonDenom n)
  have hrw : (|2-(n:ℝ)| *‖x‖*(M*‖x‖^A))*(‖x‖/2*J) = (|2-(n:ℝ)| *M*‖x‖^(A+2)*J)/2 := by
    rw [← hpower]; ring
  rw [hrw] at hh
  dsimp [C]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg (2-(n:ℝ))) hM) (Real.rpow_nonneg (norm_nonneg x) (A+2))) hJ]

end HenonLaneEmden
end
end RadialGradient

end OAI
