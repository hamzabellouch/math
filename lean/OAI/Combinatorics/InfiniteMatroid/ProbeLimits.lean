import OAI.Combinatorics.InfiniteMatroid.BlockDensity
import OAI.Combinatorics.InfiniteMatroid.Cesaro

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma finiteDensity_abs_sub {α : Type*} (s : Finset α) (X Y : Set α) :
    |finiteDensity s X - finiteDensity s Y| ≤ finiteDensity s (X ∆ Y) := by
  apply abs_le.mpr
  constructor
  · have h := (finiteDensity_mono s (show Y ⊆ X ∪ (X ∆ Y) by
      intro x hy; by_cases hx : x ∈ X; exact Or.inl hx
      exact Or.inr (by simp [symmDiff_def, hy, hx]))).trans (finiteDensity_union_le s X (X ∆ Y))
    linarith
  · have h := (finiteDensity_mono s (show X ⊆ Y ∪ (X ∆ Y) by
      intro x hx; by_cases hy : x ∈ Y; exact Or.inl hy
      exact Or.inr (by simp [symmDiff_def, hy, hx]))).trans (finiteDensity_union_le s Y (X ∆ Y))
    linarith

lemma dProbe_zero {T X : Set E0} (hX : SameClass T X) :
    Tendsto (dProbe T X) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero (fun _ ↦ abs_nonneg _) (fun m ↦ finiteDensity_abs_sub (wBlock m) X T) hX

lemma trace_prefix_card (X : Set E0) (n : ℕ) :
    (traceFinset (blockPrefix n) X).card = ∑ m ∈ range n, (traceFinset (wBlock m) X).card := by
  classical
  have he : traceFinset (blockPrefix n) X = (range n).biUnion (fun m ↦ traceFinset (wBlock m) X) := by
    ext x
    simp [mem_prefix]
  rw [he]
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact (wBlock_disjoint hij).mono (traceFinset_subset _ _) (traceFinset_subset _ _)

lemma prefix_card_atTop : Tendsto (fun n ↦ ((blockPrefix n).card : ℝ)) atTop atTop := by
  have h : ∀ n, n ≤ (blockPrefix n).card := by
    intro n
    rw [card_prefix]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have : 1 ≤ (wBlock n).card := by apply Nat.succ_le_of_lt; rw [card_wBlock]; positivity
      omega
  apply tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast h n

lemma pProbe_sum (T X : Set E0) (n : ℕ) :
    pProbe T X n = ∑ m ∈ range n, ((wBlock m).card : ℝ) * dProbe T X m := by
  rw [pProbe, trace_prefix_card, trace_prefix_card]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hc : ((wBlock m).card : ℝ) ≠ 0 := by simp
  simp only [dProbe, density, finiteDensity]
  field_simp

lemma pProbe_normalized_zero {T X : Set E0} (hX : SameClass T X) :
    Tendsto (fun n ↦ pProbe T X n / (blockPrefix n).card) atTop (𝓝 0) := by
  have hc : Tendsto (fun n ↦ ∑ m ∈ range n, ((wBlock m).card : ℝ)) atTop atTop := by
    simpa only [card_prefix, Nat.cast_sum] using prefix_card_atTop
  simpa only [pProbe_sum, card_prefix, Nat.cast_sum] using
    weighted_mean_zero (fun m ↦ ((wBlock m).card : ℝ)) (dProbe T X)
      (fun _ ↦ Nat.cast_nonneg _) hc (dProbe_zero hX)

noncomputable def errorTail (T X : Set E0) (n : ℕ) : ℝ := tailSup (fun m ↦ |dProbe T X m|) n

lemma dProbe_abs_bdd (T X : Set E0) : BddAbove (Set.range (fun m ↦ |dProbe T X m|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact abs_le.mpr (dProbe_bounds T X m)

lemma errorTail_nonneg (T X : Set E0) (n : ℕ) : 0 ≤ errorTail T X n :=
  (abs_nonneg _).trans (le_tailSup (dProbe_abs_bdd T X) le_rfl)

lemma abs_dProbe_le_errorTail (T X : Set E0) {n m : ℕ} (hnm : n ≤ m) :
    |dProbe T X m| ≤ errorTail T X n := le_tailSup (dProbe_abs_bdd T X) hnm

lemma errorTail_zero {T X : Set E0} (hX : SameClass T X) :
    Tendsto (errorTail T X) atTop (𝓝 0) :=
  tail_absSup_zero _ (dProbe_abs_bdd T X) (dProbe_zero hX)

lemma small_iff_density {G : Set E0} (hG : ¬ Small G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ m, N ≤ m ∧ δ ≤ density G m := by
  by_contra! hn
  apply hG
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hn ε hε
  refine ⟨N, fun m hm ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ density G m from finiteDensity_nonneg _ _)]
  exact hN m hm

end InfiniteMatroidCounterexample
end

end OAI
