import Mathlib

namespace OAI
/-!
# Exact dyadic decomposition of a truncated hyperbola

The long--long convolution is partitioned into genuine dyadic row intervals.
Each column interval is shortened to `N / 2^j`, retaining the exact `mn ≤ N`
cutoff. This is a finite reindexing, with no analytic cancellation hypothesis.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.VaughanDyadic

/-- Rows above the lower cutoff, inside one half-open power-of-two interval. -/
def shell (U N j : ℕ) : Finset ℕ :=
  (Ioc U N).filter fun m => 2 ^ j ≤ m ∧ m < 2 ^ (j + 1)

lemma mem_shell {U N j m : ℕ} :
    m ∈ shell U N j ↔ U < m ∧ m ≤ N ∧ 2 ^ j ≤ m ∧ m < 2 ^ (j + 1) := by
  simp only [shell, mem_filter, mem_Ioc]
  tauto

lemma shell_eq_log_fiber (U N j : ℕ) :
    shell U N j = (Ioc U N).filter (fun m => Nat.log 2 m = j) := by
  ext m
  simp only [shell, mem_filter]
  apply and_congr_right
  intro hm
  exact (Nat.log_eq_iff (Or.inr ⟨by decide, (lt_of_le_of_lt (Nat.zero_le U)
    (mem_Ioc.mp hm).1).ne'⟩)).symm

/-- The shell is a single consecutive interval, so its phase correlations remain geometric. -/
lemma shell_eq_Icc (U N j : ℕ) :
    shell U N j = Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)) := by
  ext m
  rw [mem_shell]
  simp only [mem_Icc, max_le_iff, le_min_iff]
  have hp : 0 < 2 ^ (j + 1) := by positivity
  omega

/-- Exact partition, valid also when the original interval is empty. -/
theorem sum_eq_sum_shells {E : Type*} [AddCommMonoid E]
    (U N : ℕ) (f : ℕ → E) :
    (∑ m ∈ Ioc U N, f m) =
      ∑ j ∈ range (Nat.log 2 N + 1), ∑ m ∈ shell U N j, f m := by
  simp_rw [shell_eq_log_fiber]
  apply (sum_fiberwise_of_maps_to ?_ f).symm
  intro m hm
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Ioc.mp hm).2))

lemma inner_sum_eq_common_cutoff {E : Type*} [AddCommMonoid E]
    (N U V j m : ℕ) (hm : m ∈ shell U N j) (f : ℕ → E) :
    (∑ n ∈ Ioc V (N / m), f n) =
      ∑ n ∈ Ioc V (N / 2 ^ j), if m * n ≤ N then f n else 0 := by
  have hmem := mem_shell.mp hm
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le U) hmem.1
  have hpow : 0 < 2 ^ j := by positivity
  have hdiv : N / m ≤ N / 2 ^ j := Nat.div_le_div_left hmem.2.2.1 hpow
  have hsets : Ioc V (N / m) =
      (Ioc V (N / 2 ^ j)).filter (fun n => m * n ≤ N) := by
    ext n
    simp only [mem_Ioc, mem_filter]
    constructor
    · rintro ⟨hV, hn⟩
      exact ⟨⟨hV, hn.trans hdiv⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hn⟩
    · rintro ⟨⟨hV, _⟩, hn⟩
      exact ⟨hV, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hn)⟩
  rw [hsets, sum_filter]

/-- The actual dyadic block, not a rectangular surrogate without the cutoff. -/
def block {E : Type*} [AddCommMonoid E] (N U V j : ℕ) (F : ℕ → ℕ → E) : E :=
  ∑ m ∈ shell U N j, ∑ n ∈ Ioc V (N / 2 ^ j),
    if m * n ≤ N then F m n else 0

/-- Exact long--long hyperbola decomposition into common-column dyadic blocks. -/
theorem sum_hyperbola_eq_sum_blocks {E : Type*} [AddCommMonoid E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    (∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n) =
      ∑ j ∈ range (Nat.log 2 N + 1), block N U V j F := by
  rw [sum_eq_sum_shells]
  apply sum_congr rfl
  intro j hj
  unfold block
  apply sum_congr rfl
  intro m hm
  exact inner_sum_eq_common_cutoff N U V j m hm (F m)

/-- Product-finset form of the same exact decomposition. -/
theorem sum_filtered_product_eq_sum_blocks {E : Type*} [AddCommMonoid E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    (∑ d ∈ (Ioc U N ×ˢ Ioc V N).filter (fun d => d.1 * d.2 ≤ N), F d.1 d.2) =
      ∑ j ∈ range (Nat.log 2 N + 1), block N U V j F := by
  rw [← sum_hyperbola_eq_sum_blocks, sum_filter, sum_product]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le U) (mem_Ioc.mp hm).1
  rw [← sum_filter]
  have he : (Ioc V N).filter (fun n => m * n ≤ N) = Ioc V (N / m) := by
    ext n
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hV, _⟩, hmn⟩
      exact ⟨hV, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hmn)⟩
    · rintro ⟨hV, hn⟩
      exact ⟨⟨hV, hn.trans (Nat.div_le_self N m)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hn⟩
  rw [he]

/-- Triangle inequality with the actual dyadic block norms. -/
theorem norm_hyperbola_le_sum_block_norms {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      ∑ j ∈ range (Nat.log 2 N + 1), ‖block N U V j F‖ := by
  rw [sum_hyperbola_eq_sum_blocks]
  exact norm_sum_le _ _

/-- Any genuine uniform block estimate pays only the number of dyadic blocks. -/
theorem norm_hyperbola_le_block_count {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) (B : ℝ)
    (hB : ∀ j < Nat.log 2 N + 1, ‖block N U V j F‖ ≤ B) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      (Nat.log 2 N + 1 : ℕ) * B := by
  calc
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1), ‖block N U V j F‖ :=
      norm_hyperbola_le_sum_block_norms N U V F
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1), B :=
      sum_le_sum fun j hj => hB j (mem_range.mp hj)
    _ = _ := by simp

/-- Real-log normalization of the finite dyadic block count. -/
theorem norm_hyperbola_le_log_budget {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖block N U V j F‖ ≤ B) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      (1 + Real.log N / Real.log 2) * B := by
  refine (norm_hyperbola_le_block_count N U V F B hB).trans ?_
  apply mul_le_mul_of_nonneg_right _ hB0
  have h := Real.natLog_le_logb N 2
  simp only [Real.logb, Nat.cast_ofNat] at h
  push_cast
  linarith

end Problem337.VaughanDyadic

end

end OAI
