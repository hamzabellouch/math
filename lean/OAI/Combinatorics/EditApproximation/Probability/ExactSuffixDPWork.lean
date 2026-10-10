import OAI.Combinatorics.EditApproximation.Probability.ExactSuffixDP
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A costed implementation of the exact cut dynamic program. The counter
counts symbol comparisons and list-cell visits, with explicit outer-loop
overhead. Each counted transition uses a fixed number of word operations;
the surrounding RAM realization supplies that constant. Suffix lookups and
occurrence scans are charged rather than treated as constant-time arrays. -/

namespace EditApproximation











theorem dpLength_spec {α : Type*} (word : List α) :
    (dpLength word).1 = word.length ∧ (dpLength word).2 = word.length + 1 := by
  induction word with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    constructor <;> simp only [dpLength, List.length_cons, ih.1, ih.2]

theorem dpDrop_spec {α : Type*} (n : ℕ) (word : List α) :
    (dpDrop n word).1 = word.drop n ∧ (dpDrop n word).2 ≤ word.length + 1 := by
  induction n generalizing word with
  | zero => simp only [dpDrop, List.drop_zero, le_add_iff_nonneg_left, Nat.zero_le, and_self]
  | succ n ih =>
    cases word with
    | nil => simp only [dpDrop, List.drop_nil, List.length_nil, le_refl, and_self]
    | cons first rest =>
      have h := ih rest
      exact ⟨h.1, by simpa only [dpDrop, List.length_cons] using Nat.add_le_add_right h.2 1⟩

theorem dpTake_spec {α : Type*} (n : ℕ) (word : List α) :
    (dpTake n word).1 = word.take n ∧ (dpTake n word).2 ≤ word.length + 1 := by
  induction n generalizing word with
  | zero => simp only [dpTake, List.take_zero, le_add_iff_nonneg_left, Nat.zero_le, and_self]
  | succ n ih =>
    cases word with
    | nil => simp only [dpTake, List.take_nil, List.length_nil, le_refl, and_self]
    | cons first rest =>
      have h := ih rest
      exact ⟨congrArg (List.cons first) h.1,
        by simpa only [dpTake, List.length_cons] using Nat.add_le_add_right h.2 1⟩

theorem dpGetD_spec (word : List ℕ) (n : ℕ) :
    (dpGetD word n).1 = word.getD n 0 ∧ (dpGetD word n).2 ≤ word.length + 1 := by
  induction word generalizing n with
  | nil => simp [dpGetD]
  | cons first rest ih =>
    cases n with
    | zero => simp [dpGetD]
    | succ n =>
      have h := ih n
      exact ⟨h.1, by simpa only [dpGetD, List.length_cons] using Nat.add_le_add_right h.2 1⟩

theorem dpMember_spec {α : Type*} [DecidableEq α] (a : α) (word : List α) :
    (dpMember a word).1 = decide (a ∈ word) ∧ (dpMember a word).2 ≤ word.length + 1 := by
  induction word with
  | nil => simp [dpMember]
  | cons first rest ih =>
    by_cases h : a = first
    · simp [dpMember, h]
    · constructor
      · simp only [dpMember, h, ite_false, ih.1, List.mem_cons, false_or]
      · simpa only [dpMember, h, ite_false, List.length_cons] using Nat.add_le_add_right ih.2 1



theorem dpSingleton_spec {α : Type*} [DecidableEq α] (a : α) (word : List α) :
    (dpSingleton a word).1 = singletonCost a word ∧ (dpSingleton a word).2 ≤ 2 * word.length + 4 := by
  by_cases h : word = []
  · subst word; simp [dpSingleton, singletonCost]
  · constructor
    · simp only [dpSingleton, singletonCost, h, ite_false, occurrenceDeficit, (dpLength_spec word).1,
        (dpMember_spec a word).1, decide_eq_true_eq]
    · have hc := (dpLength_spec word).2
      have hm := (dpMember_spec a word).2
      simp only [dpSingleton, h, ite_false]
      omega



theorem dpMinimum_spec (fallback : ℕ) (values : List ℕ) :
    (dpMinimum fallback values).1 = natListMinimum fallback values ∧
      (dpMinimum fallback values).2 = values.length + 1 := by
  induction values with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    constructor <;> simp only [dpMinimum, natListMinimum, ih.1, ih.2, List.length_cons]



theorem dpCandidate_value {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j k : ℕ) :
    (dpCandidate a target previous j k).1 =
      singletonCost a ((target.drop j).take k) + previous.getD (j + k) 0 := by
  simp only [dpCandidate, (dpSingleton_spec _ _).1, (dpDrop_spec _ _).1,
    (dpTake_spec _ _).1, (dpGetD_spec _ _).1]

theorem dpCandidate_work {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (hprevious : previous.length = target.length + 1) (j k : ℕ) :
    (dpCandidate a target previous j k).2 ≤ 12 * (target.length + 1) := by
  have hs := (dpDrop_spec j target).2
  have hp := (dpTake_spec k (dpDrop j target).1).2
  have ho := (dpSingleton_spec a (dpTake k (dpDrop j target).1).1).2
  have hg := (dpGetD_spec previous (j + k)).2
  have hsl : (dpDrop j target).1.length ≤ target.length := by
    rw [(dpDrop_spec _ _).1, List.length_drop]; omega
  have hpl : (dpTake k (dpDrop j target).1).1.length ≤ target.length := by
    rw [(dpTake_spec _ _).1, List.length_take]
    exact (min_le_right _ _).trans hsl
  simp only [dpCandidate]
  rw [hprevious] at hg
  omega

theorem nat_pair_sum_bound {ι : Type*} (values : List ι) (cost : ι → ℕ) (budget : ℕ)
    (h : ∀ value ∈ values, cost value ≤ budget) :
    (values.map cost).sum ≤ values.length * budget := by
  induction values with
  | nil => simp
  | cons first rest ih =>
    have hf := h first List.mem_cons_self
    have hr := ih (fun value hv => h value (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith



theorem dpCell_value {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j : ℕ) :
    (dpCell a target previous j).1 =
      natListMinimum (singletonCost a [] + previous.getD j 0)
        ((List.range (target.length - j + 1)).map fun k =>
          singletonCost a ((target.drop j).take k) + previous.getD (j + k) 0) := by
  simp only [dpCell, (dpMinimum_spec _ _).1, dpCandidate_value, List.take_zero, Nat.add_zero,
    List.map_map, Function.comp_def]

theorem dpCell_work {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (hprevious : previous.length = target.length + 1) (j : ℕ) :
    (dpCell a target previous j).2 ≤ 40 * (target.length + 1) ^ 2 := by
  let candidates := (List.range (target.length - j + 1)).map (dpCandidate a target previous j)
  have hsum := nat_pair_sum_bound candidates Prod.snd (12 * (target.length + 1)) (by
    intro candidate hc
    rcases List.mem_map.mp hc with ⟨k, _, rfl⟩
    exact dpCandidate_work a target previous hprevious j k)
  have hcount : candidates.length ≤ target.length + 1 := by
    simp only [candidates, List.length_map, List.length_range]; omega
  have hf := dpCandidate_work a target previous hprevious j 0
  have hm := (dpMinimum_spec (dpCandidate a target previous j 0).1 (candidates.map Prod.fst)).2
  simp only [List.length_map] at hm
  have hl := (dpLength_spec target).2
  change (dpCandidate a target previous j 0).2 + (candidates.map Prod.snd).sum +
    (dpMinimum (dpCandidate a target previous j 0).1 (candidates.map Prod.fst)).2 +
    (dpLength target).2 + 3 * candidates.length + 4 ≤ _
  have hprod := Nat.mul_le_mul_right (12 * (target.length + 1)) hcount
  nlinarith



theorem chargedSuffixDP_value {α : Type*} [DecidableEq α] (source target : List α) :
    (chargedSuffixDP source target).1 = exactSuffixDP source target := by
  induction source with
  | nil => rfl
  | cons a rest ih =>
    simp only [chargedSuffixDP, exactSuffixDP, List.map_ofFn, Function.comp_def, dpCell_value, ih]

theorem chargedSuffixDP_work {α : Type*} [DecidableEq α] (source target : List α) :
    (chargedSuffixDP source target).2 ≤ 50 * (source.length + 1) * (target.length + 1) ^ 3 := by
  induction source with
  | nil =>
    have hcube : target.length + 1 ≤ (target.length + 1) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ target.length + 1) (by decide : 1 ≤ 3)
    simp only [chargedSuffixDP, List.length_nil]
    omega
  | cons a rest ih =>
    let previous := chargedSuffixDP rest target
    let cells := List.ofFn fun j : Fin (target.length + 1) => dpCell a target previous.1 j.val
    have hprevious : previous.1.length = target.length + 1 := by
      rw [chargedSuffixDP_value, exactSuffixDP_length]
    have hsum := nat_pair_sum_bound cells Prod.snd (40 * (target.length + 1) ^ 2) (by
      intro cell hc
      rcases List.mem_ofFn.mp hc with ⟨j, rfl⟩
      exact dpCell_work a target previous.1 hprevious j.val)
    have hcount : cells.length = target.length + 1 := List.length_ofFn
    have hl := (dpLength_spec target).2
    change previous.2 + (cells.map Prod.snd).sum + 2 * (dpLength target).2 +
      2 * cells.length + 3 ≤ _
    change previous.2 ≤ _ at ih
    rw [hcount] at hsum ⊢
    simp only [List.length_cons]
    nlinarith [show 0 ≤ target.length by omega]

/-- Every retained row has linear length, and every stored distance fits
the input length bound; the traversal counter is polynomial even with lists. -/
theorem chargedSuffixDP_storage {α : Type*} [DecidableEq α] (source target : List α)
    (N : ℕ) (hsize : source.length + target.length ≤ N) :
    (chargedSuffixDP source target).1.length ≤ N + 1 ∧
      (∀ j ≤ target.length, (chargedSuffixDP source target).1.getD j 0 ≤ N) ∧
      (chargedSuffixDP source target).2 ≤ 50 * (N + 1) ^ 4 := by
  rw [chargedSuffixDP_value]
  constructor
  · rw [exactSuffixDP_length]; omega
  constructor
  · intro j hj
    rw [exactSuffixDP_spec source target j hj]
    apply (EditDistortion.edit_le_max_length _ _).trans
    simp only [List.length_drop]
    exact max_le (by omega) (by omega)
  · have h := chargedSuffixDP_work source target
    have hn : source.length + 1 ≤ N + 1 := by omega
    have hm : target.length + 1 ≤ N + 1 := by omega
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 50 hn) (Nat.pow_le_pow_left hm 3)
    exact h.trans (by simpa only [show (N + 1) ^ 4 = (N + 1) * (N + 1) ^ 3 by ring,
      Nat.mul_assoc] using hmul)

theorem dpTake_allocation {α : Type*} (n : ℕ) (word : List α) :
    (dpTake n word).1.length ≤ (dpTake n word).2 := by
  induction n generalizing word with
  | zero => simp [dpTake]
  | succ n ih =>
    cases word with
    | nil => simp [dpTake]
    | cons first rest => simpa only [dpTake, List.length_cons] using Nat.add_le_add_right (ih rest) 1



theorem dpCandidate_allocation {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j k : ℕ) :
    dpCandidateAllocation target j k ≤ (dpCandidate a target previous j k).2 := by
  have h := dpTake_allocation k (dpDrop j target).1
  simp only [dpCandidateAllocation, dpCandidate]
  omega

theorem nat_list_sum_mono {ι : Type*} (values : List ι) (f g : ι → ℕ)
    (h : ∀ value ∈ values, f value ≤ g value) : (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => exact le_rfl
  | cons first rest ih =>
    have hf := h first List.mem_cons_self
    have hr := ih (fun value hv => h value (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Candidate pairs, natural candidate values, the index range and prefix
lists are counted as materialized cells. The fallback prefix is retained. -/


theorem dpCell_allocation {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j : ℕ) : dpCellAllocation target j ≤ (dpCell a target previous j).2 := by
  have hf := dpCandidate_allocation a target previous j 0
  have hs := nat_list_sum_mono (List.range (target.length - j + 1))
    (dpCandidateAllocation target j) (fun k => (dpCandidate a target previous j k).2)
    (fun k _ => dpCandidate_allocation a target previous j k)
  simp only [dpCell, (dpMinimum_spec _ _).2, List.length_map, List.length_range,
    List.map_map, Function.comp_def]
  unfold dpCellAllocation
  omega

/-- Total materialized list cells over the whole run. This also bounds
the simultaneously live materialized cells under any deallocation policy. -/


theorem suffixDPAllocation_le_work {α : Type*} [DecidableEq α] (source target : List α) :
    suffixDPAllocation source target ≤ (chargedSuffixDP source target).2 := by
  induction source with
  | nil => simp only [suffixDPAllocation, chargedSuffixDP]; omega
  | cons a rest ih =>
    let previous := chargedSuffixDP rest target
    let cells := List.ofFn fun j : Fin (target.length + 1) => dpCell a target previous.1 j.val
    have hs : (List.ofFn fun j : Fin (target.length + 1) => dpCellAllocation target j.val).sum ≤
        (cells.map Prod.snd).sum := by
      simp only [cells, List.map_ofFn, List.sum_ofFn]
      exact Finset.sum_le_sum (fun j _ => dpCell_allocation a target previous.1 j.val)
    have hl := (dpLength_spec target).2
    have hc : cells.length = target.length + 1 := List.length_ofFn
    change suffixDPAllocation rest target + _ + _ ≤
      previous.2 + (cells.map Prod.snd).sum + 2 * (dpLength target).2 + 2 * cells.length + 3
    change suffixDPAllocation rest target ≤ previous.2 at ih
    omega

theorem suffixDPAllocation_polynomial {α : Type*} [DecidableEq α] (source target : List α)
    (N : ℕ) (hsize : source.length + target.length ≤ N) :
    suffixDPAllocation source target ≤ 50 * (N + 1) ^ 4 :=
  (suffixDPAllocation_le_work source target).trans (chargedSuffixDP_storage source target N hsize).2.2

end EditApproximation

end OAI
