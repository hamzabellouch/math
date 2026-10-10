import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.History

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

theorem historyLaw_past_mean {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (T j k : ℕ) (hjk : j ≤ k)
    (f : History α T → ℝ)
    (hf : ∀ ω π, (∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) → f ω = f π) :
    pmfMean (historyLaw initial K T k) f =
      pmfMean (historyLaw initial K T j) f := by
  classical
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | @succ k hjk ih =>
    change pmfMean ((historyLaw initial K T k).bind (historyKernel K T k)) f = _
    rw [pmfMean_bind]
    have he (ω : History α T) : pmfMean (historyKernel K T k ω) f = f ω := by
      by_cases hk : k < T
      · rw [historyKernel,ite_eq_left hk,pmfMean_map]
        have hu (b : α) : f (Function.update ω (historyIndex T (k+1)) b) = f ω := by
          apply hf
          intro i hi
          apply Function.update_of_ne
          intro hh
          have hval := congrArg Fin.val hh
          simp only [historyIndex,Nat.min_eq_left (by omega : k+1 ≤ T)] at hval
          have : i.val ≤ j := hi.trans (Nat.min_le_left _ _)
          omega
        simp_rw [hu]
        exact pmfMean_const _ _
      · rw [historyKernel,ite_eq_right hk,pmfMean_pure]
    simp_rw [he]
    exact ih

lemma historyNoise_past {α : Type*} [Fintype α] (K : ℕ → α → PMF α)
    (f : ℕ → α → ℝ) (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyNoise K f T j ω = historyNoise K f T j π := by
  unfold historyNoise
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  simp only [historyIncrement,h _ hsc,h _ hsn]

lemma historyCounter_past {α : Type*} (v : ℕ → α → ℝ)
    (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyCounter v T j ω = historyCounter v T j π := by
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  rw [h _ hsc]

lemma pmfMean_finset_sum {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (f : J → α → ℝ) :
    pmfMean p (fun a => ∑ j ∈ s, f j a) = ∑ j ∈ s, pmfMean p (f j) := by
  simp only [pmfMean,Finset.mul_sum]
  exact Finset.sum_comm

open Classical in

theorem pmfMean_event_union {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (P : J → α → Prop) :
    pmfMean p (fun a => if ∃ j ∈ s, P j a then 1 else 0) ≤
      ∑ j ∈ s, pmfMean p (fun a => if P j a then 1 else 0) := by
  classical
  rw [← pmfMean_finset_sum]
  apply pmfMean_mono
  intro a _
  by_cases h : ∃ j ∈ s, P j a
  · obtain ⟨j,hj,hP⟩ := h
    rw [ite_eq_left ⟨j,hj,hP⟩]
    have hh := Finset.single_le_sum (f := fun j => (if P j a then (1 : ℝ) else 0))
      (fun _ _ => by positivity) hj
    simpa only [ite_eq_left hP] using hh
  · rw [ite_eq_right h]
    positivity

theorem history_noise_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (f v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |f (k+1) b - pmfMean (K k a) (f (k+1))| ≤ c)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b =>
        (f (k+1) b - pmfMean (K k a) (f (k+1)))^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyNoise K f T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ) * Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyNoise K f T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyNoise K f T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω π h
          rw [historyNoise_past K f T j ω π h,historyCounter_past v T j ω π h])]
        exact history_noise_freedman initial K f v T c hc hbounded hvar j r V hr hV
      _ = _ := by simp
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range,Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl

end SharpTerminalLeave

end

end OAI
