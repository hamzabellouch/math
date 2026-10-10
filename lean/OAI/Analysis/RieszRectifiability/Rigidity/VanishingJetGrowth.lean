import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzSecondDifference

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set
open scoped ContDiff

theorem iteratedFDeriv_growth_of_zero_jets {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Ambient d → F) (hf : ContDiff ℝ ∞ f)
    (M : ℝ) (hM : 0 ≤ M) (n k : ℕ)
    (hz : ∀ j, n ≤ j → j < n + k → iteratedFDeriv ℝ j f 0 = 0)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (n + k) f x‖ ≤ M) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ M * ‖x‖ ^ k := by
  induction k generalizing n x with
  | zero => simpa only [Nat.add_zero, pow_zero, mul_one] using! hb x
  | succ k ih =>
    have hn : ∀ y, ‖iteratedFDeriv ℝ (n + 1) f y‖ ≤ M * ‖y‖ ^ k := by
      intro y
      apply ih (n + 1)
      · intro j hj hjk
        exact hz j (by omega) (by omega)
      · intro z
        rw [show n + 1 + k = n + (k + 1) by omega]
        exact hb z
    have hfinite : ContDiff ℝ (n + 1 : ℕ) f := hf.of_le (by exact_mod_cast le_top)
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      hfinite.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hbound : ∀ y ∈ segment ℝ (0 : Ambient d) x,
        ‖fderiv ℝ (iteratedFDeriv ℝ n f) y‖ ≤ M * ‖x‖ ^ k := by
      intro y hy
      rw [norm_fderiv_iteratedFDeriv]
      apply (hn y).trans
      have hxy : ‖y‖ ≤ ‖x‖ := by
        simpa only [sub_zero] using! norm_sub_le_of_mem_segment hy
      gcongr
    have hv := (convex_segment (0 : Ambient d) x).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hd y) hbound (left_mem_segment ℝ 0 x) (right_mem_segment ℝ 0 x)
    rw [hz n le_rfl (by omega), sub_zero, sub_zero] at hv
    simpa only [pow_succ, mul_assoc] using! hv

theorem schwartz_zero_jet_derivative_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (N j : ℕ) (hj : j ≤ N + 1)
    (hz : ∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = 0) (x : Ambient d) :
    ‖iteratedFDeriv ℝ j g x‖ ≤
      SchwartzMap.seminorm ℝ 0 (N + 1) g * ‖x‖ ^ (N + 1 - j) := by
  apply iteratedFDeriv_growth_of_zero_jets g (g.smooth ⊤)
    (SchwartzMap.seminorm ℝ 0 (N + 1) g) (apply_nonneg _ _) j (N + 1 - j)
  · intro i _ hi
    exact hz i (by omega)
  · intro y
    rw [show j + (N + 1 - j) = N + 1 by omega]
    exact norm_iteratedFDeriv_le_seminorm ℝ g (N + 1) y

end

end RieszRectifiability

end OAI
