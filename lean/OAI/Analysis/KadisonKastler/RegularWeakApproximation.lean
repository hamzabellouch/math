import OAI.Analysis.KadisonKastler.RegularIntervalCutoffs
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! # Extending bounded weak limits from cutoff vectors

Uniform operator bounds make matrix coefficients equicontinuous in each
test vector. Strongly convergent cutoff vectors therefore suffice for
identifying a weak operator limit.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem weak_tendsto_of_strong_cutoff_tests
    (A : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (P : ℕ → H →L[ℂ] H) (hP : ∀ x, Tendsto (fun k => P k x) atTop (𝓝 x))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C)
    (ht : ∀ k l x y, Tendsto (fun n => inner ℂ (P l y) (A n (P k x)))
      atTop (𝓝 (inner ℂ (P l y) (T (P k x)))))
    (x y : H) :
    Tendsto (fun n => inner ℂ y (A n x)) atTop (𝓝 (inner ℂ y (T x))) := by
  have hnorm (n : ℕ) (v : H) : ‖A n v‖ ≤ C * ‖v‖ :=
    ((A n).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg v))
  have heqY (v : H) : Equicontinuous (fun n : ℕ => fun w : H => inner ℂ w (A n v)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (NNReal.mk (C * ‖v‖) (mul_nonneg hC (norm_nonneg _)))
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, ← inner_sub_left, dist_eq_norm]
    change ‖inner ℂ (z - w) (A n v)‖ ≤ C * ‖v‖ * ‖z - w‖
    calc
      _ ≤ ‖z - w‖ * ‖A n v‖ := norm_inner_le_norm _ _
      _ ≤ ‖z - w‖ * (C * ‖v‖) := mul_le_mul_of_nonneg_left (hnorm n v) (norm_nonneg _)
      _ = _ := by ring
  have hy (k : ℕ) (w : H) :
      Tendsto (fun n => inner ℂ w (A n (P k x))) atTop
        (𝓝 (inner ℂ w (T (P k x)))) := by
    have hc := (heqY (P k x)).isClosed_setOfPred_tendsto (l := atTop)
      (show Continuous (fun w : H => inner ℂ w (T (P k x))) by fun_prop)
    exact hc.mem_of_tendsto (hP w) (Eventually.of_forall fun l => ht k l x w)
  have heqX : Equicontinuous (fun n : ℕ => fun v : H => inner ℂ y (A n v)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (NNReal.mk (C * ‖y‖) (mul_nonneg hC (norm_nonneg _)))
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm, ← inner_sub_right, ← map_sub, dist_eq_norm]
    change ‖inner ℂ y (A n (v - w))‖ ≤ C * ‖y‖ * ‖v - w‖
    calc
      _ ≤ ‖y‖ * ‖A n (v - w)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖v - w‖) := mul_le_mul_of_nonneg_left (hnorm n _) (norm_nonneg _)
      _ = _ := by ring
  have hc := heqX.isClosed_setOfPred_tendsto (l := atTop)
    (show Continuous (fun v : H => inner ℂ y (T v)) by fun_prop)
  exact hc.mem_of_tendsto (hP x) (Eventually.of_forall fun k => hy k y)

end

end KadisonKastler

end OAI
