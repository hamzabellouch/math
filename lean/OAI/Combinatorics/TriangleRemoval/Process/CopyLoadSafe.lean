import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.CopyEdgeLoad
import OAI.Combinatorics.TriangleRemoval.Process.HistoryAdditive

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

def copyLoadSafe {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (G : Graph n) : Prop :=
  ∀ e ∈ G, copyEdgeLoad required G e ≤ L

noncomputable def safeCopyIncrement {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (_j : ℕ) (G H : Graph n) : ℝ := by
  classical
  exact if copyLoadSafe required L G then
    copyCount required H - pmfMean (step G) (copyCount required) else 0

noncomputable def safeCopyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (j : ℕ) (G : Graph n) : ℝ := by
  classical
  exact if copyLoadSafe required L G then copyVarianceRate required L j G else 0

theorem triangle_safe_template_freedman {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L : ℝ) (hL : 0 < L)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        r ≤ historyAdditive (safeCopyIncrement required L) T j ω ∧
        historyCounter (safeCopyVarianceRate required L) T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+(3*L)*r))) := by
  classical
  apply history_additive_freedman_maximal (PMF.pure G) (fun _ => step)
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

def pastCopyLoadsSafe {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (T j : ℕ) (ω : History (Graph n) T) : Prop :=
  ∀ s < min j T, copyLoadSafe required L (ω (historyIndex T s))

lemma safeCopyNoise_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (T j : ℕ) (ω : History (Graph n) T)
    (hs : pastCopyLoadsSafe required L T j ω) :
    historyAdditive (safeCopyIncrement required L) T j ω =
      historyNoise (fun _ => step) (fun _ => copyCount required) T j ω := by
  classical
  unfold historyAdditive historyNoise
  apply Finset.sum_congr rfl
  intro s hsm
  simp only [historyIncrement,safeCopyIncrement,ite_eq_left (hs s (Finset.mem_range.mp hsm))]

lemma safeCopyCounter_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (T j : ℕ) (ω : History (Graph n) T)
    (hs : pastCopyLoadsSafe required L T j ω) :
    historyCounter (safeCopyVarianceRate required L) T j ω =
      historyCounter (copyVarianceRate required L) T j ω := by
  classical
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro s hsm
  simp only [safeCopyVarianceRate,ite_eq_left (hs s (Finset.mem_range.mp hsm))]

open Classical in

theorem triangle_template_before_load_exit {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L : ℝ) (hL : 0 < L)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T, pastCopyLoadsSafe required L T j ω ∧
        r ≤ historyNoise (fun _ => step) (fun _ => copyCount required) T j ω ∧
        historyCounter (copyVarianceRate required L) T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+(3*L)*r))) := by
  apply le_trans _ (triangle_safe_template_freedman required G T L hL r V hr hV)
  apply pmfMean_mono
  intro ω _
  by_cases h : ∃ j ≤ T, pastCopyLoadsSafe required L T j ω ∧
      r ≤ historyNoise (fun _ => step) (fun _ => copyCount required) T j ω ∧
      historyCounter (copyVarianceRate required L) T j ω ≤ V
  · obtain ⟨j,hj,hs,hn,hc⟩ := h
    have h' : ∃ j ≤ T, r ≤ historyAdditive (safeCopyIncrement required L) T j ω ∧
        historyCounter (safeCopyVarianceRate required L) T j ω ≤ V := by
      refine ⟨j,hj,?_,?_⟩
      · rwa [safeCopyNoise_eq required L T j ω hs]
      · rwa [safeCopyCounter_eq required L T j ω hs]
    rw [ite_eq_left ⟨j,hj,hs,hn,hc⟩,ite_eq_left h']
  · rw [ite_eq_right h]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI
