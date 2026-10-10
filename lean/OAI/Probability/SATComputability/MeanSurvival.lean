import OAI.Probability.SATComputability.CandidateProbability

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal BigOperators Classical

theorem candidateBlock_survival_antitone {n : ℕ} [NeZero n] (k : ℕ)
    (U : Finset (DeletionCandidate n)) :
    Antitone (fun r => (candidateBlock r k U).expect candidateAlive) := by
  intro r s hrs
  simp only [candidateBlock_expect_alive]
  exact sub_le_sub_left (poissonKillProbability_mono_rate U k hrs) 1

theorem survival_le_mean_lifetime {n M t : ℕ} [NeZero n]
    (ht : t ≤ M) (U : Finset (DeletionCandidate n)) :
    (t : ℝ)*(candidateBlock (n := n) t 3 U).expect candidateAlive ≤
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock (n := n) 1 3 Finset.univ)).expect
        (maskLifetime M U) := by
  rw [maskLifetime_mean]
  simp only [one_mul]
  calc
    _ = ∑ _s ∈ Finset.range t, (candidateBlock (n := n) t 3 U).expect candidateAlive := by
      simp
    _ ≤ ∑ s ∈ Finset.range t, (candidateBlock (n := n) s 3 U).expect candidateAlive := by
      apply Finset.sum_le_sum
      intro s hs
      exact candidateBlock_survival_antitone 3 U (by exact_mod_cast
        (Finset.mem_range.mp hs).le)
    _ ≤ ∑ s ∈ Finset.range M, (candidateBlock (n := n) s 3 U).expect candidateAlive := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
      intro s _ _
      exact FiniteLaw.expect_nonneg _ candidateAlive_nonneg

theorem antitone_sum_bound (q : ℕ → ℝ) (hq : Antitone q)
    (h0 : ∀ s, 0 ≤ q s) (h1 : ∀ s, q s ≤ 1) (M t : ℕ) :
    ∑ s ∈ Finset.range M, q s ≤ t + (M : ℝ)*q t := by
  by_cases ht : t ≤ M
  · rw [← Nat.add_sub_of_le ht, Finset.sum_range_add]
    have hfirst : ∑ s ∈ Finset.range t, q s ≤ (t : ℝ) := by
      calc
        _ ≤ ∑ _s ∈ Finset.range t, (1 : ℝ) := Finset.sum_le_sum (fun s _ => h1 s)
        _ = _ := by simp
    have hlast : ∑ s ∈ Finset.range (M-t), q (t+s) ≤ (M-t : ℕ)*q t := by
      calc
        _ ≤ ∑ _s ∈ Finset.range (M-t), q t :=
          Finset.sum_le_sum (fun s _ => hq (Nat.le_add_right t s))
        _ = _ := by simp
    have htail : ((M-t : ℕ) : ℝ)*q t ≤ (t+(M-t) : ℕ)*q t :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left (M-t) t) (h0 t)
    push_cast at htail ⊢
    linarith
  · have hMt : M ≤ t := (Nat.lt_of_not_ge ht).le
    calc
      _ ≤ ∑ _s ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum (fun s _ => h1 s)
      _ = M := by simp
      _ ≤ t := by exact_mod_cast hMt
      _ ≤ t + (M : ℝ)*q t := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg M) (h0 t))

theorem zero_lifetime_mean_upper (n : ℕ) [NeZero n] (b : ℝ≥0) :
    (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
      (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤
        ⌈(b : ℝ)*n⌉₊ + (20*n : ℕ)*auxiliaryPoissonProbability n b := by
  rw [maskLifetime_mean]
  simp only [one_mul]
  have h := antitone_sum_bound
    (fun s => (candidateBlock (n := n) s 3 (deletionBudgetMask n 0)).expect candidateAlive)
    (fun s t hst => candidateBlock_survival_antitone 3 _ (by exact_mod_cast hst))
    (fun _ => FiniteLaw.expect_nonneg _ candidateAlive_nonneg)
    (fun _ => (FiniteLaw.expect_mono _ candidateAlive_le_one).trans_eq (FiniteLaw.expect_const _ 1))
    (20*n) ⌈(b : ℝ)*n⌉₊
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hb : b*n ≤ (⌈(b : ℝ)*n⌉₊ : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using Nat.le_ceil ((b : ℝ)*n)
  have hs := candidateBlock_survival_antitone 3 (deletionBudgetMask n 0) hb
  simpa only [candidateBlock_zero_survival, auxiliaryPoissonProbability] using hs

theorem minimumDeletions_survival_lower {n r : ℕ} (hr : r ≤ n+1)
    (U : Finset (DeletionCandidate n)) :
    (r : ℝ)*(1-candidateAlive (U ∩ deletionBudgetMask n r)) ≤ minimumDeletions U := by
  by_cases h : (U ∩ deletionBudgetMask n r).Nonempty
  · simp only [candidateAlive, ite_eq_left h, sub_self, mul_zero]
    exact Nat.cast_nonneg _
  · simp only [candidateAlive, ite_eq_right h, sub_zero, mul_one]
    by_cases hU : U.Nonempty
    · have hm : r < minimumDeletions U := by
        apply Nat.lt_of_not_ge
        intro hm
        obtain ⟨x,hx,hxr⟩ := (minimumDeletions_le_iff hU).mp hm
        exact h ⟨x,Finset.mem_inter.mpr ⟨hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxr⟩⟩⟩
      exact_mod_cast hm.le
    · rw [minimumDeletions, dite_eq_right hU]
      exact_mod_cast hr

theorem block_minimumDeletions_lower {n r : ℕ} [NeZero n] (hr : r ≤ n+1) (t : ℝ≥0) :
    (r : ℝ)*(1-(candidateBlock t 3 (deletionBudgetMask n r)).expect candidateAlive) ≤
      (candidateBlock (n := n) t 3 Finset.univ).expect (fun U => (minimumDeletions U : ℝ)) := by
  have h := (candidateBlock (n := n) t 3 Finset.univ).expect_mono
    (minimumDeletions_survival_lower hr)
  rw [FiniteLaw.expect_mul_left, FiniteLaw.expect_sub, FiniteLaw.expect_const] at h
  have he : (candidateBlock (n := n) t 3 Finset.univ).expect
      (fun x => candidateAlive (x ∩ deletionBudgetMask n r)) =
      (candidateBlock t 3 (deletionBudgetMask n r)).expect candidateAlive := by
    calc
      _ = (candidateBlock (n := n) t 3 Finset.univ).expect
          (fun x => candidateAlive (deletionBudgetMask n r ∩ x)) :=
        FiniteLaw.expect_congr _ (fun x => congrArg candidateAlive (Finset.inter_comm x _))
      _ = _ := candidateBlock_mask t 3 (deletionBudgetMask n r) candidateAlive
  rwa [he] at h

end FixedClauseThreshold.Computability

end OAI
