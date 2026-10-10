import OAI.Analysis.MarkovType.FiniteStoppingTime
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.SplitIfs

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω : Type*}

def selectionPredicate (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) (n : ℕ) : Prop :=
  0 < n ∧ n ≤ N ∧ B n ω

def selectionCount (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) : ℕ :=
  Nat.count (selectionPredicate N B ω) (N + 1)

def selectionSlot (N : ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) : ℕ :=
  if i < selectionCount N B ω then Nat.nth (selectionPredicate N B ω) i else N + 1

def selectionTime (N : ℕ) (B : ℕ → Ω → Prop) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | i + 1 => selectionSlot N B i

@[simp] theorem selectionTime_zero (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionTime N B 0 ω = 0 := rfl

@[simp] theorem selectionTime_succ (N : ℕ) (B : ℕ → Ω → Prop) (i : ℕ) (ω : Ω) :
    selectionTime N B (i + 1) ω = selectionSlot N B i ω := rfl

theorem selectionSlot_mem {N i : ℕ} {B : ℕ → Ω → Prop} {ω : Ω}
    (hi : i < selectionCount N B ω) :
    selectionPredicate N B ω (selectionSlot N B i ω) := by
  rw [selectionSlot, ite_eq_left hi]
  exact Nat.nth_mem i (fun hf => hi.trans_le (Nat.count_le_card hf (N + 1)))

theorem selectionSlot_rank {N i : ℕ} {B : ℕ → Ω → Prop} {ω : Ω}
    (hi : i < selectionCount N B ω) :
    Nat.count (selectionPredicate N B ω) (selectionSlot N B i ω) = i := by
  rw [selectionSlot, ite_eq_left hi]
  exact Nat.count_nth (fun hf => hi.trans_le (Nat.count_le_card hf (N + 1)))

theorem selectionSlot_pos (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    0 < selectionSlot N B i ω := by
  by_cases hi : i < selectionCount N B ω
  · exact (selectionSlot_mem hi).1
  · simp only [selectionSlot, ite_eq_right hi]
    exact Nat.succ_pos N

theorem selectionSlot_le (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionSlot N B i ω ≤ N + 1 := by
  by_cases hi : i < selectionCount N B ω
  · exact (selectionSlot_mem hi).2.1.trans (Nat.le_succ N)
  · simp only [selectionSlot, ite_eq_right hi, le_refl]

theorem selectionSlot_le_horizon_iff (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionSlot N B i ω ≤ N ↔ i < selectionCount N B ω := by
  by_cases hi : i < selectionCount N B ω
  · exact ⟨fun _ => hi, fun _ => (selectionSlot_mem hi).2.1⟩
  · simp [selectionSlot, hi]

theorem selectionSlot_eq_sentinel_iff (N i : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionSlot N B i ω = N + 1 ↔ selectionCount N B ω ≤ i := by
  by_cases hi : i < selectionCount N B ω
  · have hle := (selectionSlot_mem hi).2.1
    have hne : selectionSlot N B i ω ≠ N + 1 := by omega
    simp [hne, Nat.not_le.mpr hi]
  · simp [selectionSlot, hi, Nat.le_of_not_gt hi]

theorem selectionSlot_eq_iff {N i n : ℕ} (B : ℕ → Ω → Prop) (ω : Ω)
    (hn : n ≤ N) :
    selectionSlot N B i ω = n ↔
      selectionPredicate N B ω n ∧ Nat.count (selectionPredicate N B ω) n = i := by
  constructor
  · intro h
    have hi : i < selectionCount N B ω :=
      (selectionSlot_le_horizon_iff N i B ω).mp (h.symm ▸ hn)
    exact ⟨h ▸ selectionSlot_mem hi, h ▸ selectionSlot_rank hi⟩
  · rintro ⟨hp, hrank⟩
    have hi : i < selectionCount N B ω := by
      rw [← hrank]
      exact Nat.count_strict_mono hp (Nat.lt_succ_of_le hn)
    rw [selectionSlot, ite_eq_left hi, ← hrank, Nat.nth_count hp]

theorem selectionSlot_monotone (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    Monotone (fun i => selectionSlot N B i ω) := by
  intro i j hij
  by_cases hj : j < selectionCount N B ω
  · have hi := hij.trans_lt hj
    simp only [selectionSlot, ite_eq_left hi, ite_eq_left hj]
    exact Nat.nth_le_nth' hij (fun hf => hj.trans_le (Nat.count_le_card hf (N + 1)))
  · calc
      selectionSlot N B i ω ≤ N + 1 := selectionSlot_le N i B ω
      _ = selectionSlot N B j ω := by simp only [selectionSlot, ite_eq_right hj]

theorem selectionSlot_strict_before_horizon {N i j : ℕ} (B : ℕ → Ω → Prop)
    (ω : Ω) (hij : i < j) (hj : selectionSlot N B j ω ≤ N) :
    selectionSlot N B i ω < selectionSlot N B j ω := by
  have hj' := (selectionSlot_le_horizon_iff N j B ω).mp hj
  have hi := hij.trans hj'
  simp only [selectionSlot, ite_eq_left hi, ite_eq_left hj']
  exact Nat.nth_lt_nth' hij (fun hf => hj'.trans_le (Nat.count_le_card hf (N + 1)))

theorem selectionTime_monotone (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    Monotone (fun i => selectionTime N B i ω) := by
  intro i j hij
  cases i with
  | zero => exact Nat.zero_le _
  | succ i =>
    cases j with
    | zero => omega
    | succ j => exact selectionSlot_monotone N B ω (Nat.succ_le_succ_iff.mp hij)

theorem selectionTime_strict_before_horizon {N i : ℕ} (B : ℕ → Ω → Prop)
    (ω : Ω) (hi : selectionTime N B (i + 1) ω ≤ N) :
    selectionTime N B i ω < selectionTime N B (i + 1) ω := by
  cases i with
  | zero => exact selectionSlot_pos N 0 B ω
  | succ i => exact selectionSlot_strict_before_horizon B ω (Nat.lt_succ_self i) hi

private theorem count_congr_below (P Q : ℕ → Prop) (n : ℕ)
    (h : ∀ j, j < n → (P j ↔ Q j)) : Nat.count P n = Nat.count Q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun hj => h j hj)

theorem selectionCount_before_congr (F : FinitePartitionFiltration Ω)
    (N : ℕ) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    {n : ℕ} {ω η : Ω} (hωη : (F.part (n - 1)).r ω η) :
    Nat.count (selectionPredicate N B ω) n = Nat.count (selectionPredicate N B η) n := by
  apply count_congr_below
  intro j hj
  by_cases hjpos : 0 < j
  · by_cases hjN : j ≤ N
    · have hrel : (F.part (j - 1)).r ω η :=
        F.refines (Nat.sub_le_sub_right (Nat.le_of_lt hj) 1) hωη
      simp only [selectionPredicate, hjpos, hjN, true_and]
      exact hB j hjpos hjN hrel
    · simp only [selectionPredicate, hjN, false_and, and_false]
  · simp only [selectionPredicate, hjpos, false_and]

theorem selectionSlot_predictable (F : FinitePartitionFiltration Ω)
    (N : ℕ) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    (i : ℕ) : F.IsPredictableTime (selectionSlot N B i) := by
  intro n hn ω η hωη
  by_cases hnN : n ≤ N
  · rw [selectionSlot_eq_iff B ω hnN, selectionSlot_eq_iff B η hnN,
      selectionCount_before_congr F N B hB hωη]
    have hBn := hB n hn hnN hωη
    simp only [selectionPredicate, hn, hnN, true_and, hBn]
  · by_cases hnSent : n = N + 1
    · subst n
      rw [selectionSlot_eq_sentinel_iff, selectionSlot_eq_sentinel_iff]
      have hc := selectionCount_before_congr F N B hB (n := N + 1) hωη
      change Nat.count (selectionPredicate N B ω) (N + 1) ≤ i ↔
        Nat.count (selectionPredicate N B η) (N + 1) ≤ i
      rw [hc]
    · have hω := selectionSlot_le N i B ω
      have hη := selectionSlot_le N i B η
      have hneω : selectionSlot N B i ω ≠ n := by omega
      have hneη : selectionSlot N B i η ≠ n := by omega
      simp only [hneω, hneη]

theorem selectionTime_stopping (F : FinitePartitionFiltration Ω)
    (N : ℕ) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    (i : ℕ) : F.IsStoppingTime (selectionTime N B i) := by
  cases i with
  | zero => exact F.isStoppingTime_const 0
  | succ i =>
    exact F.isStoppingTime_of_isPredictableTime
      (selectionSlot_pos N i B) (selectionSlot_predictable F N B hB i)

theorem sum_selectionSlot {V : Type*} [AddCommMonoid V]
    (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) (f : ℕ → V) :
    (∑ i ∈ Finset.range (selectionCount N B ω), f (selectionSlot N B i ω)) =
      ∑ n ∈ (Finset.range (N + 1)).filter (selectionPredicate N B ω), f n := by
  apply Finset.sum_bij (fun i _ => selectionSlot N B i ω)
  · intro i hi
    have hmem := selectionSlot_mem (Finset.mem_range.mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmem.2.1), hmem⟩
  · intro i hi j hj hij
    have hirank := selectionSlot_rank (Finset.mem_range.mp hi)
    have hjrank := selectionSlot_rank (Finset.mem_range.mp hj)
    rw [hij] at hirank
    exact hirank.symm.trans hjrank
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnrange, hnP⟩
    refine ⟨Nat.count (selectionPredicate N B ω) n, ?_, ?_⟩
    · exact Finset.mem_range.mpr
        (Nat.count_strict_mono hnP (Finset.mem_range.mp hnrange))
    · exact (selectionSlot_eq_iff B ω hnP.2.1).mpr ⟨hnP, rfl⟩
  · intro i hi
    rfl

theorem sum_selectionSlot_padded {V : Type*} [AddCommMonoid V]
    (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) (f : ℕ → V) (J : ℕ)
    (hJ : selectionCount N B ω ≤ J) :
    (∑ i ∈ Finset.range J,
      if selectionSlot N B i ω ≤ N then f (selectionSlot N B i ω) else 0) =
      ∑ n ∈ Finset.range (N + 1), if selectionPredicate N B ω n then f n else 0 := by
  calc
    _ = ∑ i ∈ Finset.range (selectionCount N B ω),
        if selectionSlot N B i ω ≤ N then f (selectionSlot N B i ω) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hJ)
      intro i hi hin
      have hnot : ¬i < selectionCount N B ω := fun h => hin (Finset.mem_range.mpr h)
      have hnotN : ¬selectionSlot N B i ω ≤ N :=
        fun h => hnot ((selectionSlot_le_horizon_iff N i B ω).mp h)
      exact ite_eq_right hnotN
    _ = ∑ i ∈ Finset.range (selectionCount N B ω), f (selectionSlot N B i ω) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (selectionSlot_mem (Finset.mem_range.mp hi)).2.1
    _ = ∑ n ∈ (Finset.range (N + 1)).filter (selectionPredicate N B ω), f n :=
      sum_selectionSlot N B ω f
    _ = _ := by rw [Finset.sum_filter]

end MarkovSuperreflexivity

end

end OAI
