import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Process.CopyLoadSafe
import OAI.Combinatorics.TriangleRemoval.Probability.PmfMeanNeg

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem triangle_safe_template_freedman_two_sided {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L : ℝ) (hL : 0 < L)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        r ≤ |historyAdditive (safeCopyIncrement required L) T j ω| ∧
        historyCounter (safeCopyVarianceRate required L) T j ω ≤ V then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+(3*L)*r))) := by
  classical
  apply history_additive_freedman_two_sided (PMF.pure G) (fun _ => step)
    (safeCopyIncrement required L) (safeCopyVarianceRate required L) T (3*L) (by positivity)
  · intro j _ H _ J hJ
    by_cases hs : copyLoadSafe required L H
    · simp only [safeCopyIncrement,ite_eq_left hs]
      exact pmf_centered_of_loss_range (step H) (copyCount required) (copyCount required H)
        (3*L) (fun A hA => copyCount_step_loss_range required H A L hL.le hs hA) J hJ
    · simp only [safeCopyIncrement,ite_eq_right hs,abs_zero]
      positivity
  · intro j _ H _
    change pmfMean (step H) (fun J => safeCopyIncrement required L j H J) = 0
    by_cases hs : copyLoadSafe required L H
    · simp only [safeCopyIncrement,ite_eq_left hs]
      rw [pmfMean_sub,pmfMean_const,sub_self]
    · simp only [safeCopyIncrement,ite_eq_right hs,pmfMean_const]
  · intro j _ H _
    by_cases hs : copyLoadSafe required L H
    · simp only [safeCopyIncrement,safeCopyVarianceRate,ite_eq_left hs]
      exact pmf_variance_of_loss_range (step H) (copyCount required) (copyCount required H)
        (3*L) (fun A hA => copyCount_step_loss_range required H A L hL.le hs hA)
    · simp only [safeCopyIncrement,safeCopyVarianceRate,ite_eq_right hs,zero_pow (by decide : 2 ≠ 0),
        pmfMean_const,le_refl]
  · exact hr
  · exact hV

open Classical in

theorem triangle_template_before_load_exit_two_sided {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L : ℝ) (hL : 0 < L)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T, pastCopyLoadsSafe required L T j ω ∧
        r ≤ |historyNoise (fun _ => step) (fun _ => copyCount required) T j ω| ∧
        historyCounter (copyVarianceRate required L) T j ω ≤ V then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+(3*L)*r))) := by
  apply le_trans _ (triangle_safe_template_freedman_two_sided required G T L hL r V hr hV)
  apply pmfMean_mono
  intro ω _
  by_cases h : ∃ j ≤ T, pastCopyLoadsSafe required L T j ω ∧
      r ≤ |historyNoise (fun _ => step) (fun _ => copyCount required) T j ω| ∧
      historyCounter (copyVarianceRate required L) T j ω ≤ V
  · obtain ⟨j,hj,hs,hn,hc⟩ := h
    have h' : ∃ j ≤ T, r ≤ |historyAdditive (safeCopyIncrement required L) T j ω| ∧
        historyCounter (safeCopyVarianceRate required L) T j ω ≤ V := by
      refine ⟨j,hj,?_,?_⟩
      · rwa [safeCopyNoise_eq required L T j ω hs]
      · rwa [safeCopyCounter_eq required L T j ω hs]
    rw [ite_eq_left ⟨j,hj,hs,hn,hc⟩,ite_eq_left h']
  · rw [ite_eq_right h]
    split <;> norm_num

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
