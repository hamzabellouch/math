import OAI.NumberTheory.JointDickman.Probability.FiniteChannelSchur
import OAI.NumberTheory.JointDickman.Probability.ResidueCentering

namespace OAI

/-!
# Uniform residue attenuation from a two-split kernel estimate

This is the finite operator step in the residue-flattening argument. Its
hypothesis concerns the kernel, and its conclusion holds simultaneously
for every input, including an input chosen using an external parameter.
-/

namespace JointDickman

open Finset

/-- A uniform residue-independent kernel approximation controls the whole
unit ball of the channel, rather than just a fixed input. -/
theorem residueChannel_square_bound {Ω D R : Type*}
    [Fintype Ω] [Fintype D] [Fintype R] [Nonempty R]
    (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hμ : ∀ d, 0 < μ d)
    (G : D → D → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hK : ∀ d e r s,
      |finiteTwoSplitKernel w (fun a : D × R => μ a.1) p (d, r) (e, s) - G d e| ≤ ε)
    (f : Ω → ℝ) :
    (∑ a : D × R, μ a.1 *
      (finiteChannel w (fun a : D × R => μ a.1) p f a -
        finiteResidueAverage (fun t => finiteChannel w (fun a : D × R => μ a.1) p f (a.1, t))) ^ 2) ≤
      (4 * ε * ∑ a : D × R, μ a.1) * ∑ s, w s * f s ^ 2 := by
  have hrow (a : D × R) :
      (∑ b : D × R, μ b.1 * |finiteTwoSplitKernel w (fun a : D × R => μ a.1)
        (residueCenteredTransition p) a b|) ≤ 4 * ε * ∑ b : D × R, μ b.1 := by
    calc
      _ ≤ ∑ b : D × R, μ b.1 * (4 * ε) := by
        apply sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left
          (finiteTwoSplitKernel_centered_abs_le w μ p G hK a.1 b.1 a.2 b.2)
          (hμ b.1).le
      _ = _ := by rw [← sum_mul]; ring
  have hbound := finiteChannel_square_of_kernel_rows w (fun a : D × R => μ a.1)
    (residueCenteredTransition p) hw (fun a => hμ a.1)
    (mul_nonneg (mul_nonneg (by norm_num) hε)
      (sum_nonneg fun a _ => (hμ a.1).le)) hrow f
  convert hbound using 1
  apply sum_congr rfl
  intro a _
  rw [finiteChannel_residueCentered]

end JointDickman

end OAI
