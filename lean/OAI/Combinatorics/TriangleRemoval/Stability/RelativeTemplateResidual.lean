import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeScaleBudget
import OAI.Combinatorics.TriangleRemoval.Process.TriangleLiftCount

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def relativeTemplateResidual {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (s : ℕ → ℝ) (T j : ℕ)
    (ω : History (Graph n) T) : ℝ :=
  copyCount required (ω (historyIndex T j))/s j -
    copyCount required (ω (historyIndex T 0))/s 0 -
    historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω +
    historyCounter (fun k G => triangleLiftCount required G/
      ((triangles G).card*s (k+1))) T j ω -
    ∑ k ∈ Finset.range j,
      copyCount required (ω (historyIndex T k))*(1/s (k+1)-1/s k)

lemma relativeTemplateResidual_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (s : ℕ → ℝ) (T j : ℕ) (hj : j ≤ T)
    (ω : History (Graph n) T) :
    relativeTemplateResidual required s T j ω = historyCounter
      (fun k G => (pmfMean (step G) (copyCount required)-copyCount required G+
        triangleLiftCount required G/(triangles G).card)/s (k+1)) T j ω := by
  have hid := history_relative_loss_counter (fun _ => step) (copyCount required) s T j hj ω
  have hsum : historyCounter
      (fun k G => (pmfMean (step G) (copyCount required)-copyCount required G+
        triangleLiftCount required G/(triangles G).card)/s (k+1)) T j ω =
      historyCounter (fun k G => triangleLiftCount required G/
        ((triangles G).card*s (k+1))) T j ω -
      historyCounter (fun k G => (copyCount required G-
        pmfMean (step G) (copyCount required))/s (k+1)) T j ω := by
    unfold historyCounter
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hsum,hid]
  unfold relativeTemplateResidual
  ring

theorem history_relative_template_hierarchy {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (b : ℕ) (hsize : ∀ a, (required a).card ≤ b)
    (s : ℕ → ℝ) (T j : ℕ) (hj : j ≤ T) (hs : ∀ k < j, 0 < s (k+1))
    (ω : History (Graph n) T) :
    0 ≤ relativeTemplateResidual required s T j ω ∧
    relativeTemplateResidual required s T j ω ≤ historyCounter
      (fun k G => ((b : ℝ)^2/(triangles G).card*copyCount required G)/s (k+1)) T j ω := by
  rw [relativeTemplateResidual_eq required s T j hj]
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    have hkj : k < j := by simpa only [Nat.min_eq_left hj,Finset.mem_range] using hk
    exact div_nonneg (copyCount_triangleLift_drift_all required
      (ω (historyIndex T k)) b hsize).1 (hs k hkj).le
  · apply Finset.sum_le_sum
    intro k hk
    have hkj : k < j := by simpa only [Nat.min_eq_left hj,Finset.mem_range] using hk
    exact div_le_div_of_nonneg_right (copyCount_triangleLift_drift_all required
      (ω (historyIndex T k)) b hsize).2 (hs k hkj).le

end SharpTerminalLeave

end

end OAI
