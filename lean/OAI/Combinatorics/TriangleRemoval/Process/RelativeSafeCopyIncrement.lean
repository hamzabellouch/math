import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.CopyLoadSafe
import OAI.Combinatorics.TriangleRemoval.Probability.PmfMeanNeg

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

noncomputable def relativeSafeCopyIncrement {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (j : ℕ) (G H : Graph n) : ℝ := by
  classical
  exact if copyLoadSafe required (L j) G then
    (copyCount required H - pmfMean (step G) (copyCount required)) / s (j+1) else 0

noncomputable def relativeCopyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (j : ℕ) (G : Graph n) : ℝ :=
  copyVarianceRate required (L j) j G / (s (j+1))^2

noncomputable def relativeSafeCopyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (j : ℕ) (G : Graph n) : ℝ := by
  classical
  exact if copyLoadSafe required (L j) G then relativeCopyVarianceRate required L s j G
    else 0

theorem triangle_relative_safe_template_freedman {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hs : ∀ j < T, 0 < s (j+1)) (hL : ∀ j < T, 0 ≤ L j)
    (hjump : ∀ j < T, 3*L j / s (j+1) ≤ c)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        r ≤ |historyAdditive (relativeSafeCopyIncrement required L s) T j ω| ∧
        historyCounter (relativeSafeCopyVarianceRate required L s) T j ω ≤ V
        then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  apply history_additive_freedman_two_sided (PMF.pure G) (fun _ => step)
    (relativeSafeCopyIncrement required L s) (relativeSafeCopyVarianceRate required L s)
    T c hc
  · intro j hj H _ J hJ
    by_cases hsafe : copyLoadSafe required (L j) H
    · simp only [relativeSafeCopyIncrement,ite_eq_left hsafe,abs_div,abs_of_pos (hs j hj)]
      exact (div_le_div_of_nonneg_right
        (pmf_centered_of_loss_range (step H) (copyCount required) (copyCount required H)
          (3*L j) (fun A hA => copyCount_step_loss_range required H A (L j)
            (hL j hj) hsafe hA) J hJ) (hs j hj).le).trans (hjump j hj)
    · simp only [relativeSafeCopyIncrement,ite_eq_right hsafe,abs_zero]
      exact hc.le
  · intro j _ H _
    change pmfMean (step H) (fun J => relativeSafeCopyIncrement required L s j H J) = 0
    by_cases hsafe : copyLoadSafe required (L j) H
    · simp only [relativeSafeCopyIncrement,ite_eq_left hsafe,div_eq_mul_inv]
      rw [pmfMean_mul_const,pmfMean_sub,pmfMean_const,sub_self,zero_mul]
    · simp only [relativeSafeCopyIncrement,ite_eq_right hsafe,pmfMean_const]
  · intro j hj H _
    by_cases hsafe : copyLoadSafe required (L j) H
    · simp only [relativeSafeCopyIncrement,relativeSafeCopyVarianceRate,ite_eq_left hsafe,
        div_eq_mul_inv,mul_pow,inv_pow]
      rw [pmfMean_mul_const]
      change _ ≤ (3*L j*(copyCount required H - pmfMean (step H) (copyCount required))) *
        ((s (j+1))^2)⁻¹
      exact mul_le_mul_of_nonneg_right
        (pmf_variance_of_loss_range (step H) (copyCount required) (copyCount required H)
          (3*L j) (fun A hA => copyCount_step_loss_range required H A (L j)
            (hL j hj) hsafe hA)) (inv_nonneg.mpr (sq_nonneg _))
    · simp only [relativeSafeCopyIncrement,relativeSafeCopyVarianceRate,ite_eq_right hsafe,
        zero_pow (by decide : 2 ≠ 0),pmfMean_const,le_refl]
  · exact hr
  · exact hV

def pastRelativeCopyLoadsSafe {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℕ → ℝ) (T j : ℕ) (ω : History (Graph n) T) : Prop :=
  ∀ k < min j T, copyLoadSafe required (L k) (ω (historyIndex T k))

lemma relativeSafeCopyNoise_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (T j : ℕ) (ω : History (Graph n) T)
    (hsafe : pastRelativeCopyLoadsSafe required L T j ω) :
    historyAdditive (relativeSafeCopyIncrement required L s) T j ω =
      historyNoise (fun _ => step) (fun k H => copyCount required H / s k) T j ω := by
  classical
  unfold historyAdditive historyNoise
  apply Finset.sum_congr rfl
  intro k hk
  simp only [historyIncrement,relativeSafeCopyIncrement,
    ite_eq_left (hsafe k (Finset.mem_range.mp hk)),div_eq_mul_inv,pmfMean_mul_const,sub_mul]

lemma relativeSafeCopyCounter_eq {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (T j : ℕ) (ω : History (Graph n) T)
    (hsafe : pastRelativeCopyLoadsSafe required L T j ω) :
    historyCounter (relativeSafeCopyVarianceRate required L s) T j ω =
      historyCounter (relativeCopyVarianceRate required L s) T j ω := by
  classical
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro k hk
  simp only [relativeSafeCopyVarianceRate,ite_eq_left (hsafe k (Finset.mem_range.mp hk))]

open Classical in

theorem triangle_relative_template_before_load_exit {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hs : ∀ j < T, 0 < s (j+1)) (hL : ∀ j < T, 0 ≤ L j)
    (hjump : ∀ j < T, 3*L j / s (j+1) ≤ c)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
        r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H / s k) T j ω| ∧
        historyCounter (relativeCopyVarianceRate required L s) T j ω ≤ V then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  apply le_trans _ (triangle_relative_safe_template_freedman required G T L s c hc hs hL
    hjump r V hr hV)
  apply pmfMean_mono
  intro ω _
  by_cases h : ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
      r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H / s k) T j ω| ∧
      historyCounter (relativeCopyVarianceRate required L s) T j ω ≤ V
  · obtain ⟨j,hj,hsafe,hn,hv⟩ := h
    have h' : ∃ j ≤ T,
        r ≤ |historyAdditive (relativeSafeCopyIncrement required L s) T j ω| ∧
        historyCounter (relativeSafeCopyVarianceRate required L s) T j ω ≤ V := by
      refine ⟨j,hj,?_,?_⟩
      · rwa [relativeSafeCopyNoise_eq required L s T j ω hsafe]
      · rwa [relativeSafeCopyCounter_eq required L s T j ω hsafe]
    rw [ite_eq_left ⟨j,hj,hsafe,hn,hv⟩,ite_eq_left h']
  · rw [ite_eq_right h]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI
