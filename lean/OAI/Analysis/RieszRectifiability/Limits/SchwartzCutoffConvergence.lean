import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem schwartz_cutoff_error_seminorm_le
    (g : 𝓢(Ambient d, F)) (q : Ambient d → ℝ) (hq : q.HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i)
    (R : ℝ) (hR : 0 < R) (hzero : ∀ x ∈ ball (0 : Ambient d) R, q x = 0)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F q g) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
        SchwartzMap.seminorm ℝ (k + 1) (n - i) g) / R := by
  have hM : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
      SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hC i))
      (apply_nonneg _ _)
  apply seminorm_le_bound ℝ k n _ (div_nonneg hM hR.le)
  intro x
  rw [smulLeftCLM_apply hq]
  by_cases hx : x ∈ ball (0 : Ambient d) R
  · have heq : (fun y => q y • g y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hzero y hy]
    have he := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [he]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using! div_nonneg hM hR.le
  · have hxR : R ≤ ‖x‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using! hx
    have hp := norm_iteratedFDeriv_smul_le hq.1 (g.smooth ⊤) x (n := n) (mod_cast le_top)
    apply (le_div_iff₀ hR).2
    calc
      (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖) * R ≤
          R * ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i q x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg (norm_nonneg x) k)]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i q x‖ *
            (R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
        apply Finset.sum_le_sum
        intro i _
        have hw : R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
            SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
          calc
            _ ≤ ‖x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) := by gcongr
            _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) g x‖ := by ring
            _ ≤ _ := le_seminorm ℝ (k + 1) (n - i) g x
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound i x) (by positivity)) hw
          (by positivity) (mul_nonneg (by positivity) (hC i))

theorem schwartz_cutoff_errors_tendsto_zero
    (g : 𝓢(Ambient d, F)) (q : ℕ → Ambient d → ℝ)
    (hq : ∀ j, (q j).HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ j i x, ‖iteratedFDeriv ℝ i (q j) x‖ ≤ C i)
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    (hzero : ∀ j x, x ∈ ball (0 : Ambient d) (R j) → q j x = 0) :
    Tendsto (fun j => smulLeftCLM F (q j) g) atTop (𝓝 0) := by
  apply (schwartz_withSeminorms ℝ (Ambient d) F).tendsto_nhds _ _ |>.2
  rintro ⟨k, n⟩ ε hε
  let M := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
    SchwartzMap.seminorm ℝ (k + 1) (n - i) g
  have ht : Tendsto (fun j => M / R j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using! tendsto_const_nhds.mul hRt.inv_tendsto_atTop
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
  simpa only [sub_zero, schwartzSeminormFamily_apply] using!
    (schwartz_cutoff_error_seminorm_le g (q j) (hq j) C hC (hbound j)
      (R j) (hR j) (hzero j) k n).trans_lt hj

end

end RieszRectifiability

end OAI
