import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-! The varying-vector step in the constrained pressure limit.

Uniformly bounded pressure operators may be tested on strongly convergent
vectors, using convergence of their quadratic forms on fixed vectors.
-/

open Filter Topology
namespace DefocusingNLS

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spectral_quadratic_difference_bound (P : E →L[ℝ] E) (u v : E) :
    ‖inner ℝ (P u) u-inner ℝ (P v) v‖ ≤
      ‖P‖*‖u-v‖*(‖u‖+‖v‖) := by
  have he : inner ℝ (P u) u-inner ℝ (P v) v=
      inner ℝ (P (u-v)) u+inner ℝ (P v) (u-v) := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℝ (P (u-v)) u‖+‖inner ℝ (P v) (u-v)‖ := norm_add_le _ _
    _ ≤ ‖P (u-v)‖*‖u‖+‖P v‖*‖u-v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖P‖*‖u-v‖)*‖u‖+(‖P‖*‖v‖)*‖u-v‖ := by
      gcongr
      · exact P.le_opNorm _
      · exact P.le_opNorm _
    _ = _ := by ring

theorem spectral_quadratic_tendsto (P : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ n, ‖P n‖ ≤ C) (u : ℕ → E) (v : E)
    (hu : Tendsto u atTop (𝓝 v)) (q : ℝ)
    (hq : Tendsto (fun n => inner ℝ (P n v) v) atTop (𝓝 q)) :
    Tendsto (fun n => inner ℝ (P n (u n)) (u n)) atTop (𝓝 q) := by
  obtain ⟨M,hM⟩ := hu.norm.isBoundedUnder_le
  have hdist : Tendsto (fun n => ‖u n-v‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hu.sub (tendsto_const_nhds (x := v))).norm
  have hb : Tendsto (fun n => C*‖u n-v‖*(M+‖v‖)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      (tendsto_const_nhds.mul hdist).mul (tendsto_const_nhds (x := M+‖v‖))
  have hd : Tendsto
      (fun n => inner ℝ (P n (u n)) (u n)-inner ℝ (P n v) v) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hb
    filter_upwards [hM] with n hn
    apply (spectral_quadratic_difference_bound (P n) (u n) v).trans
    gcongr
    · exact hP n
    · exact hn
  simpa only [sub_add_cancel,zero_add] using hd.add hq

theorem spectral_penalty_limit_zero (P : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ n, ‖P n‖ ≤ C) (u : ℕ → E) (v : E)
    (hu : Tendsto u atTop (𝓝 v)) (q : ℝ)
    (hq : Tendsto (fun n => inner ℝ (P n v) v) atTop (𝓝 q))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (K : ℝ)
    (henergy : ∀ n, 0 ≤ inner ℝ (P n (u n)) (u n) ∧
      inner ℝ (P n (u n)) (u n) ≤ K*a n) : q=0 := by
  have hz : Tendsto (fun n => inner ℝ (P n (u n)) (u n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (henergy n).1) (fun n => (henergy n).2)
    simpa only [mul_zero] using tendsto_const_nhds.mul ha
  exact tendsto_nhds_unique (spectral_quadratic_tendsto P C hC hP u v hu q hq) hz

end
end DefocusingNLS

end OAI
