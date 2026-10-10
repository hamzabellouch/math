import Mathlib
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

lemma pmfMean_neg {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    pmfMean p (fun a => -f a) = -pmfMean p f := by
  simp only [pmfMean,mul_neg,Finset.sum_neg_distrib]

lemma historyAdditive_neg {α : Type*} (g : ℕ → α → α → ℝ)
    (T j : ℕ) (ω : History α T) :
    historyAdditive (fun k a b => -g k a b) T j ω = -historyAdditive g T j ω := by
  simp only [historyAdditive,Finset.sum_neg_distrib]

theorem history_additive_freedman_two_sided {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hp := history_additive_freedman_maximal initial K g v T c hc hbounded hmean hvar r V hr hV
  have hn := history_additive_freedman_maximal initial K (fun k a b => -g k a b) v T c hc
    (by intro k hk a ha b hb; simpa only [abs_neg] using hbounded k hk a ha b hb)
    (by intro k hk a ha; rw [pmfMean_neg,hmean k hk a ha,neg_zero])
    (by intro k hk a ha; simpa only [neg_sq] using hvar k hk a ha) r V hr hV
  have hcov : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧ historyCounter v T j ω ≤ V
        then 1 else 0) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0) +
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) := by
    rw [← pmfMean_add]
    apply pmfMean_mono
    intro ω _
    by_cases h : ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧ historyCounter v T j ω ≤ V
    · obtain ⟨j,hj,hx,hv⟩ := h
      rw [ite_eq_left ⟨j,hj,hx,hv⟩]
      rcases le_total 0 (historyAdditive g T j ω) with hx0 | hx0
      · rw [abs_of_nonneg hx0] at hx
        rw [ite_eq_left ⟨j,hj,hx,hv⟩]
        split_ifs <;> norm_num
      · rw [abs_of_nonpos hx0] at hx
        have hneg : r ≤ historyAdditive (fun k a b => -g k a b) T j ω := by
          rwa [historyAdditive_neg]
        have hnegE : ∃ j ≤ T, r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V := ⟨j,hj,hneg,hv⟩
        rw [ite_eq_left hnegE]
        split_ifs <;> norm_num
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  exact hcov.trans (by nlinarith [hp,hn])

end SharpTerminalLeave

end

end OAI
