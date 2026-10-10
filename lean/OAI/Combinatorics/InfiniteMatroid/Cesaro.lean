import Mathlib

namespace OAI

section
open Filter Finset
open scoped Topology

namespace InfiniteMatroidCounterexample

/-- An elementary weighted Cesàro estimate. -/
lemma weighted_mean_zero (w d : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hc : Tendsto (fun n ↦ ∑ m ∈ range n, w m) atTop atTop)
    (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n ↦ (∑ m ∈ range n, w m * d m) / (∑ m ∈ range n, w m)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hd (ε/2) (by linarith)
  let C := ∑ m ∈ range N, |w m * d m|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hdiv : Tendsto (fun n ↦ C / (∑ m ∈ range n, w m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hc
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hdiv (ε/2) (by linarith)
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hc.eventually (eventually_gt_atTop (0:ℝ)))
  refine ⟨max N (max M L), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnL : L ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hpos := hL n hnL
  have hb : (∑ m ∈ range n, |w m * d m|) ≤ C + ε/2 * (∑ m ∈ range n, w m) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
    rw [Finset.sum_range_add]
    change C + _ ≤ _
    apply add_le_add_right
    calc
      ∑ m ∈ range k, |w (N+m) * d (N+m)| ≤ ∑ m ∈ range k, ε/2 * w (N+m) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [abs_mul, abs_of_nonneg (hw _), mul_comm]
        apply mul_le_mul_of_nonneg_right _ (hw _)
        have h := hN (N+m) (by omega)
        simpa only [Real.dist_eq, sub_zero] using h.le
      _ = ε/2 * (∑ m ∈ range k, w (N+m)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ε/2 * (∑ m ∈ range (N+k), w m) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [Finset.sum_range_add]
        have := Finset.sum_nonneg (s := range N) (fun m _ ↦ hw m)
        linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos]
  calc
    |∑ m ∈ range n, w m * d m| / (∑ m ∈ range n, w m) ≤
        (C + ε/2 * (∑ m ∈ range n, w m)) / (∑ m ∈ range n, w m) := by
      exact div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans hb) hpos.le
    _ = C / (∑ m ∈ range n, w m) + ε/2 := by field_simp
    _ < ε := by
      have h := hM n hnM
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hC hpos.le)] at h
      linarith

/-- A tail supremum of absolute values of a null sequence is again null. -/
lemma tail_absSup_zero (d : ℕ → ℝ) (hb : BddAbove (Set.range (fun n ↦ |d n|)))
    (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n ↦ sSup ((fun m ↦ |d m|) '' Set.Ici n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hd (ε/2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hne : ((fun m ↦ |d m|) '' Set.Ici n).Nonempty := ⟨|d n|, Set.mem_image_of_mem _ (show n ∈ Set.Ici n from (by simp))⟩
  have hb' : BddAbove ((fun m ↦ |d m|) '' Set.Ici n) := hb.mono (Set.image_subset_range ..)
  have hlo : 0 ≤ sSup ((fun m ↦ |d m|) '' Set.Ici n) :=
    (abs_nonneg (d n)).trans (le_csSup hb' (Set.mem_image_of_mem _ (show n ∈ Set.Ici n from (by simp))))
  have hhi : sSup ((fun m ↦ |d m|) '' Set.Ici n) ≤ ε/2 := by
    apply csSup_le hne
    rintro _ ⟨m, hm, rfl⟩
    have h := hN m (hn.trans hm)
    simpa only [Real.dist_eq, sub_zero] using h.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end InfiniteMatroidCounterexample
end

end OAI
