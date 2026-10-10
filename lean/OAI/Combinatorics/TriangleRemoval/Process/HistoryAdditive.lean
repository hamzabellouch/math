import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.HistoryLawPastMean

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

noncomputable def historyAdditive {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), g j (ω (historyIndex T j)) (ω (historyIndex T (j+1)))

lemma historyAdditive_update {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyAdditive g T (k+1) (Function.update ω (historyIndex T (k+1)) b) =
      historyAdditive g T k ω + g k (ω (historyIndex T k)) b := by
  unfold historyAdditive
  rw [Nat.min_eq_left (by omega : k+1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    rw [Function.update_of_ne (historyIndex_ne_succ hjk.le hk),
       Function.update_of_ne (historyIndex_ne_succ (by omega : j+1 ≤ k) hk)]
  · rw [Function.update_self,Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

@[simp] lemma historyAdditive_zero {α : Type*} (g : ℕ → α → α → ℝ)
    (T : ℕ) (ω : History α T) : historyAdditive g T 0 ω = 0 := by
  simp [historyAdditive]

lemma historyAdditive_frozen {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : T ≤ k) (ω : History α T) :
    historyAdditive g T (k+1) ω = historyAdditive g T k ω := by
  simp only [historyAdditive,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k+1)]

theorem history_additive_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyAdditive g T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyAdditive_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact (hmean j hj _ (historyLaw_current_support initial K T j hj.le ω hω)).le
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ π hπ
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hπ
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hπ
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hπ
      subst π
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV

lemma historyAdditive_past {α : Type*} (g : ℕ → α → α → ℝ)
    (T j : ℕ) (ω π : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyAdditive g T j ω = historyAdditive g T j π := by
  unfold historyAdditive
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  rw [h _ hsc,h _ hsn]

theorem history_additive_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω π h
          rw [historyAdditive_past g T j ω π h,historyCounter_past v T j ω π h])]
        exact history_additive_freedman initial K g v T c hc hbounded hmean hvar j r V hr hV
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
