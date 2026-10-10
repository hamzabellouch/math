import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Structure.OrderedBasis

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W29

open Submodule

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [DecidableEq ι]

def rowSpan (row : ι → V) (s : Finset ι) : Submodule K V :=
  span K (row '' (s : Set ι))

noncomputable def insertIfIndependent (row : ι → V) (s : Finset ι) (i : ι) : Finset ι :=
  by classical exact if row i ∈ rowSpan (K := K) row s then s else insert i s

def processed (indices : ℕ → ι) (n : ℕ) : Finset ι :=
  (Finset.range n).image indices

noncomputable def retained (row : ι → V) (indices : ℕ → ι) : ℕ → Finset ι
  | 0 => ∅
  | n + 1 => insertIfIndependent (K := K) row (retained row indices n) (indices n)

lemma rowSpan_insert (row : ι → V) (s : Finset ι) (i : ι) :
    rowSpan (K := K) row (insert i s) = K ∙ row i ⊔ rowSpan (K := K) row s := by
  simp [rowSpan, Set.image_insert_eq, Submodule.span_insert]

lemma insertIfIndependent_span (row : ι → V) (s : Finset ι) (i : ι) :
    rowSpan (K := K) row (insertIfIndependent (K := K) row s i) =
      rowSpan (K := K) row (insert i s) := by
  classical
  unfold insertIfIndependent
  split_ifs with h
  · symm
    simpa only [rowSpan, Finset.coe_insert, Set.image_insert_eq] using
      (Submodule.span_insert_eq_span h)
  · rfl

lemma insertIfIndependent_independent (row : ι → V) (s : Finset ι) (i : ι)
    (hs : LinearIndepOn K row (s : Set ι)) :
    LinearIndepOn K row (insertIfIndependent (K := K) row s i : Set ι) := by
  classical
  unfold insertIfIndependent
  split_ifs with h
  · exact hs
  · simpa only [Finset.coe_insert] using hs.insert h

lemma insertIfIndependent_subset (row : ι → V) (s : Finset ι) (i : ι) :
    insertIfIndependent (K := K) row s i ⊆ insert i s := by
  classical
  unfold insertIfIndependent
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

@[simp] lemma processed_zero (indices : ℕ → ι) : processed indices 0 = ∅ := by
  simp [processed]

@[simp] lemma processed_succ (indices : ℕ → ι) (n : ℕ) :
    processed indices (n + 1) = insert (indices n) (processed indices n) := by
  simp [processed, Finset.range_add_one]

theorem retained_subset_processed (row : ι → V) (indices : ℕ → ι) (n : ℕ) :
    retained (K := K) row indices n ⊆ processed indices n := by
  induction n with
  | zero => simp [retained]
  | succ n ih =>
    rw [retained, processed_succ]
    exact (insertIfIndependent_subset row _ _).trans (Finset.insert_subset_insert _ ih)

theorem retained_independent (row : ι → V) (indices : ℕ → ι) (n : ℕ) :
    LinearIndepOn K row (retained (K := K) row indices n : Set ι) := by
  induction n with
  | zero => simp [retained]
  | succ n ih => exact insertIfIndependent_independent row _ _ ih

theorem retained_span (row : ι → V) (indices : ℕ → ι) (n : ℕ) :
    rowSpan (K := K) row (retained (K := K) row indices n) =
      rowSpan (K := K) row (processed indices n) := by
  induction n with
  | zero => simp [retained]
  | succ n ih =>
    rw [retained, processed_succ, insertIfIndependent_span,
      rowSpan_insert, rowSpan_insert, ih]

theorem earlier_row_mem_retained_span (row : ι → V) (indices : ℕ → ι)
    {m n : ℕ} (hmn : m < n) :
    row (indices m) ∈ rowSpan (K := K) row (retained (K := K) row indices n) := by
  rw [retained_span]
  apply Submodule.subset_span
  refine ⟨indices m, ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmn, rfl⟩

theorem retained_weight_bound (row : ι → V) (indices : ℕ → ι)
    (weight : ι → ℕ) (n bound : ℕ)
    (hbound : ∀ m < n, weight (indices m) ≤ bound) :
    ∀ i ∈ retained (K := K) row indices n, weight i ≤ bound := by
  intro i hi
  have hp := retained_subset_processed row indices n hi
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
  exact hbound m (Finset.mem_range.mp hm)

theorem cutoff_mem_retained_span (row : ι → V) (indices : ℕ → ι)
    (weight : ι → ℕ) (n bound : ℕ)
    (hcomplete : ∀ i, weight i ≤ bound → ∃ m < n, indices m = i)
    {i : ι} (hi : weight i ≤ bound) :
    row i ∈ rowSpan (K := K) row (retained (K := K) row indices n) := by
  obtain ⟨m, hm, rfl⟩ := hcomplete i hi
  exact earlier_row_mem_retained_span row indices hm

end WeightedTorusJets.W29



namespace SiegelZerosAwei.W31

abbrev MultiIndex := Fin 3 → ℕ

def weight (H : ℝ) (a : MultiIndex) : ℝ :=
  (a 0 : ℝ) + H * (a 1 : ℝ) + H * (a 2 : ℝ)

theorem scale_identity {H : ℝ} (hH : 0 < H) :
    H * H ^ (-(1 / 3 : ℝ)) = H ^ (2 / 3 : ℝ) := by
  have h := Real.rpow_add hH (1 : ℝ) (-(1 / 3 : ℝ))
  norm_num at h
  exact h.symm

theorem rectangle_weight_le {H U : ℝ} (hH : 0 < H) (a : MultiIndex)
    (h0 : (a 0 : ℝ) ≤ 32 * H ^ (2 / 3 : ℝ) * U)
    (h1 : (a 1 : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U)
    (h2 : (a 2 : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U) :
    weight H a ≤ 96 * H ^ (2 / 3 : ℝ) * U := by
  have h1' := mul_le_mul_of_nonneg_left h1 hH.le
  have h2' := mul_le_mul_of_nonneg_left h2 hH.le
  have heq : H * (32 * H ^ (-(1 / 3 : ℝ)) * U) =
      32 * H ^ (2 / 3 : ℝ) * U := by
    calc
      _ = 32 * (H * H ^ (-(1 / 3 : ℝ))) * U := by ring
      _ = _ := by rw [scale_identity hH]
  rw [heq] at h1' h2'
  dsimp [weight]
  linarith

theorem short_coordinate_sum_le {H U : ℝ} (hH : 0 < H) (a : MultiIndex)
    (hcut : weight H a ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (a 1 : ℝ) + (a 2 : ℝ) ≤ 96 * H ^ (-(1 / 3 : ℝ)) * U := by
  apply (mul_le_mul_iff_right₀ hH).mp
  calc
    H * ((a 1 : ℝ) + (a 2 : ℝ)) ≤ 96 * H ^ (2 / 3 : ℝ) * U := by
      dsimp [weight] at hcut
      have h0 : 0 ≤ (a 0 : ℝ) := Nat.cast_nonneg _
      nlinarith
    _ = H * (96 * H ^ (-(1 / 3 : ℝ)) * U) := by
      rw [← scale_identity hH]
      ring

theorem short_coordinates_le {H U : ℝ} (hH : 0 < H) (a : MultiIndex)
    (hcut : weight H a ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (a 1 : ℝ) ≤ 96 * H ^ (-(1 / 3 : ℝ)) * U ∧
      (a 2 : ℝ) ≤ 96 * H ^ (-(1 / 3 : ℝ)) * U := by
  have h := short_coordinate_sum_le hH a hcut
  have h1 : 0 ≤ (a 1 : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ (a 2 : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

theorem short_sum_le_96 {H U : ℝ} (hH : 0 < H) (P : Finset MultiIndex)
    (hcut : ∀ a ∈ P, weight H a ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (∑ a ∈ P, ((a 1 : ℝ) + (a 2 : ℝ))) ≤
      96 * (P.card : ℝ) * H ^ (-(1 / 3 : ℝ)) * U := by
  calc
    _ ≤ ∑ _a ∈ P, 96 * H ^ (-(1 / 3 : ℝ)) * U :=
      Finset.sum_le_sum (fun a ha => short_coordinate_sum_le hH a (hcut a ha))
    _ = _ := by simp [mul_assoc, mul_comm]

theorem short_sum_le_192 {H U : ℝ} (hH : 0 < H) (hU : 0 ≤ U)
    (P : Finset MultiIndex)
    (hcut : ∀ a ∈ P, weight H a ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (∑ a ∈ P, ((a 1 : ℝ) + (a 2 : ℝ))) ≤
      192 * (P.card : ℝ) * H ^ (-(1 / 3 : ℝ)) * U := by
  have h := short_sum_le_96 hH P hcut
  have hp : 0 ≤ (P.card : ℝ) * H ^ (-(1 / 3 : ℝ)) * U :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hH.le _)) hU
  nlinarith

theorem pivot_S2_bound (H N : ℕ) (hH : 0 < H) (P : Finset MultiIndex)
    (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (((∑ a ∈ P, (a 1 + a 2)) : ℕ) : ℝ) ≤
      192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) *
        (N : ℝ) ^ (4 / 3 : ℝ) := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hU : 0 ≤ (N : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h := short_sum_le_192 hH' hU P hcut
  simpa only [Nat.cast_sum, Nat.cast_add, hcard, Nat.cast_pow] using h

end SiegelZerosAwei.W31



namespace WeightedTorusJets.W29

open Submodule
open scoped Classical

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [DecidableEq ι]

lemma subset_insertIfIndependent (row : ι → V) (s : Finset ι) (i : ι) :
    s ⊆ insertIfIndependent (K := K) row s i := by
  classical
  unfold insertIfIndependent
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.subset_insert _ _

theorem retained_monotone (row : ι → V) (indices : ℕ → ι) :
    Monotone (retained (K := K) row indices) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_insertIfIndependent row _ _

omit [DecidableEq ι] in
lemma not_mem_of_row_not_mem_span (row : ι → V) (s : Finset ι) (i : ι)
    (hi : row i ∉ rowSpan (K := K) row s) : i ∉ s := by
  intro his
  apply hi
  exact Submodule.subset_span ⟨i, his, rfl⟩

theorem retained_card_succ (row : ι → V) (indices : ℕ → ι) (n : ℕ) :
    (retained (K := K) row indices (n + 1)).card =
      if row (indices n) ∈ rowSpan (K := K) row (processed indices n)
      then (retained (K := K) row indices n).card
      else (retained (K := K) row indices n).card + 1 := by
  classical
  rw [← retained_span row indices n]
  rw [retained, insertIfIndependent]
  split_ifs with h
  · rfl
  · exact Finset.card_insert_of_notMem (not_mem_of_row_not_mem_span row _ _ h)

theorem retained_succ_of_dependent (row : ι → V) (indices : ℕ → ι) (n : ℕ)
    (h : row (indices n) ∈ rowSpan (K := K) row (processed indices n)) :
    retained (K := K) row indices (n + 1) = retained (K := K) row indices n := by
  classical
  rw [← retained_span row indices n] at h
  simp only [retained, insertIfIndependent, ite_eq_left h]

theorem retained_succ_of_independent (row : ι → V) (indices : ℕ → ι) (n : ℕ)
    (h : row (indices n) ∉ rowSpan (K := K) row (processed indices n)) :
    retained (K := K) row indices (n + 1) =
      insert (indices n) (retained (K := K) row indices n) := by
  classical
  rw [← retained_span row indices n] at h
  simp only [retained, insertIfIndependent, ite_eq_right h]

end WeightedTorusJets.W29



namespace WeightedTorusJets.W29

open Submodule

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [LinearOrder ι]

def finiteEnumeration (s : Finset ι) (fallback : ι) (n : ℕ) : ι :=
  if h : n < s.card then s.orderEmbOfFin rfl ⟨n, h⟩ else fallback

lemma finiteEnumeration_mem (s : Finset ι) (fallback : ι) {n : ℕ} (hn : n < s.card) :
    finiteEnumeration s fallback n ∈ s := by
  simp only [finiteEnumeration, dite_eq_left hn]
  exact s.orderEmbOfFin_mem rfl _

lemma finiteEnumeration_complete (s : Finset ι) (fallback : ι) {i : ι} (hi : i ∈ s) :
    ∃ n < s.card, finiteEnumeration s fallback n = i := by
  have hirange : i ∈ Set.range (s.orderEmbOfFin rfl) := by
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hi
  obtain ⟨n, hn⟩ := hirange
  exact ⟨n.val, n.isLt, by simpa only [finiteEnumeration, dite_eq_left n.isLt] using hn⟩

theorem finiteEnumeration_strictMono (s : Finset ι) (fallback : ι)
    {m n : ℕ} (hmn : m < n) (hn : n < s.card) :
    finiteEnumeration s fallback m < finiteEnumeration s fallback n := by
  have hm : m < s.card := hmn.trans hn
  simp only [finiteEnumeration, dite_eq_left hm, dite_eq_left hn]
  exact (s.orderEmbOfFin rfl).strictMono hmn

theorem finiteEnumeration_weight_mono (s : Finset ι) (fallback : ι)
    (weight : ι → ℕ) (hw : MonotoneOn weight (s : Set ι))
    {m n : ℕ} (hmn : m < n) (hn : n < s.card) :
    weight (finiteEnumeration s fallback m) ≤ weight (finiteEnumeration s fallback n) := by
  exact hw (finiteEnumeration_mem s fallback (hmn.trans hn))
    (finiteEnumeration_mem s fallback hn)
    (finiteEnumeration_strictMono s fallback hmn hn).le

theorem processed_finiteEnumeration (s : Finset ι) (fallback : ι) :
    processed (finiteEnumeration s fallback) s.card = s := by
  ext i
  constructor
  · intro hi
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi
    exact finiteEnumeration_mem s fallback (Finset.mem_range.mp hn)
  · intro hi
    obtain ⟨n, hn, hni⟩ := finiteEnumeration_complete s fallback hi
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, hni⟩

noncomputable def finiteSelection (row : ι → V) (s : Finset ι) (fallback : ι) : Finset ι :=
  retained (K := K) row (finiteEnumeration s fallback) s.card

theorem finiteSelection_independent (row : ι → V) (s : Finset ι) (fallback : ι) :
    LinearIndepOn K row (finiteSelection (K := K) row s fallback : Set ι) :=
  retained_independent row _ _

theorem finiteSelection_span (row : ι → V) (s : Finset ι) (fallback : ι) :
    rowSpan (K := K) row (finiteSelection (K := K) row s fallback) =
      rowSpan (K := K) row s := by
  rw [finiteSelection, retained_span, processed_finiteEnumeration]

theorem finiteSelection_subset (row : ι → V) (s : Finset ι) (fallback : ι) :
    finiteSelection (K := K) row s fallback ⊆ s := by
  simpa only [finiteSelection, processed_finiteEnumeration] using
    (retained_subset_processed (K := K) row (finiteEnumeration s fallback) s.card)

theorem finiteSelection_span_top (row : ι → V) (s : Finset ι) (fallback : ι)
    (hspan : rowSpan (K := K) row s = ⊤) :
    rowSpan (K := K) row (finiteSelection (K := K) row s fallback) = ⊤ := by
  rw [finiteSelection_span, hspan]

end WeightedTorusJets.W29



namespace WeightedTorusJets.W29

open Submodule

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [LinearOrder ι]

theorem retained_prefix_subset_earlier (row : ι → V) (s : Finset ι) (fallback : ι)
    {n : ℕ} (hn : n < s.card) :
    retained (K := K) row (finiteEnumeration s fallback) n ⊆
      (finiteSelection (K := K) row s fallback).filter
        (fun x => x < finiteEnumeration s fallback n) := by
  intro x hx
  have hfinal : x ∈ finiteSelection (K := K) row s fallback :=
    retained_monotone row (finiteEnumeration s fallback) hn.le hx
  have hprocessed := retained_subset_processed row (finiteEnumeration s fallback) n hx
  obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp hprocessed
  apply Finset.mem_filter.mpr
  refine ⟨hfinal, ?_⟩
  rw [← hmx]
  exact finiteEnumeration_strictMono s fallback (Finset.mem_range.mp hm) hn

theorem earlier_row_mem_final_earlier_span (row : ι → V) (s : Finset ι)
    (fallback : ι) {m n : ℕ} (hmn : m < n) (hn : n < s.card) :
    row (finiteEnumeration s fallback m) ∈
      rowSpan (K := K) row ((finiteSelection (K := K) row s fallback).filter
        (fun x => x < finiteEnumeration s fallback n)) := by
  have hspan : rowSpan (K := K) row
      (retained (K := K) row (finiteEnumeration s fallback) n) ≤
      rowSpan (K := K) row ((finiteSelection (K := K) row s fallback).filter
        (fun x => x < finiteEnumeration s fallback n)) := by
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, retained_prefix_subset_earlier row s fallback hn hx, rfl⟩
  exact hspan (earlier_row_mem_retained_span row (finiteEnumeration s fallback) hmn)

theorem lower_index_mem_selected_span (row : ι → V) (s : Finset ι)
    (fallback : ι) {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) :
    row a ∈ rowSpan (K := K) row
      ((finiteSelection (K := K) row s fallback).filter (fun x => x < b)) := by
  obtain ⟨m, hm, hma⟩ := finiteEnumeration_complete s fallback ha
  obtain ⟨n, hn, hnb⟩ := finiteEnumeration_complete s fallback hb
  have hmn : m < n := by
    by_contra h
    have hnm : n ≤ m := Nat.le_of_not_gt h
    have hba : b ≤ a := by
      rw [← hnb, ← hma]
      rcases lt_or_eq_of_le hnm with hlt | heq
      · exact (finiteEnumeration_strictMono s fallback hlt hm).le
      · rw [heq]
    exact (not_le_of_gt hab) hba
  simpa only [hma, hnb] using
    earlier_row_mem_final_earlier_span row s fallback hmn hn

end WeightedTorusJets.W29



namespace WeightedTorusJets.W62

structure Index (H : ℕ) where
  coords : Fin 3 → ℕ
  deriving DecidableEq

def weight {H : ℕ} (a : Index H) : ℕ :=
  a.coords 0 + H * a.coords 1 + H * a.coords 2

def key {H : ℕ} (a : Index H) : ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex (weight a, toLex (a.coords 0, toLex (a.coords 1, a.coords 2)))

theorem key_injective {H : ℕ} : Function.Injective (@key H) := by
  intro a b hab
  have h := congrArg (fun k => (ofLex k).2) hab
  have h0 := congrArg (fun k => (ofLex k).1) h
  have h12 := congrArg (fun k => (ofLex k).2) h
  have h1 := congrArg (fun k => (ofLex k).1) h12
  have h2 := congrArg (fun k => (ofLex k).2) h12
  have hc : a.coords = b.coords := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  cases a
  cases b
  cases hc
  rfl

instance (H : ℕ) : LinearOrder (Index H) := LinearOrder.lift' key key_injective

theorem lt_of_weight_lt {H : ℕ} {a b : Index H} (h : weight a < weight b) : a < b := by
  change key a < key b
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem weight_monotone {H : ℕ} : Monotone (@weight H) := by
  intro a b hab
  change key a ≤ key b at hab
  exact (Prod.Lex.toLex_le_toLex'.mp hab).1

theorem coordinate_le_weight {H : ℕ} (hH : 0 < H) (a : Index H) (i : Fin 3) :
    a.coords i ≤ weight a := by
  have h1 : a.coords 1 ≤ H * a.coords 1 := by nlinarith
  have h2 : a.coords 2 ≤ H * a.coords 2 := by nlinarith
  unfold weight
  fin_cases i
  · change a.coords 0 ≤ a.coords 0 + H * a.coords 1 + H * a.coords 2
    omega
  · change a.coords 1 ≤ a.coords 0 + H * a.coords 1 + H * a.coords 2
    omega
  · change a.coords 2 ≤ a.coords 0 + H * a.coords 1 + H * a.coords 2
    omega

def cutoff (H C : ℕ) : Finset (Index H) :=
  ((Fintype.piFinset fun _ : Fin 3 => Finset.range (C + 1)).image Index.mk).filter
    (fun a => weight a ≤ C)

@[simp] theorem mem_cutoff {H C : ℕ} (hH : 0 < H) (a : Index H) :
    a ∈ cutoff H C ↔ weight a ≤ C := by
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).2
  · intro ha
    apply Finset.mem_filter.mpr
    refine ⟨?_, ha⟩
    apply Finset.mem_image.mpr
    refine ⟨a.coords, ?_, rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_range.mpr (by have := coordinate_le_weight hH a i; omega)

def zeroIndex (H : ℕ) : Index H := ⟨fun _ => 0⟩

def enumeration (H C : ℕ) : ℕ → Index H :=
  W29.finiteEnumeration (cutoff H C) (zeroIndex H)

theorem enumeration_weight_le {H C n : ℕ} (hH : 0 < H)
    (hn : n < (cutoff H C).card) : weight (enumeration H C n) ≤ C :=
  (mem_cutoff hH _).mp (W29.finiteEnumeration_mem _ _ hn)

theorem enumeration_complete {H C : ℕ} (hH : 0 < H) (a : Index H)
    (ha : weight a ≤ C) :
    ∃ n < (cutoff H C).card, enumeration H C n = a :=
  W29.finiteEnumeration_complete _ _ ((mem_cutoff hH a).mpr ha)

theorem enumeration_strictMono {H C m n : ℕ} (hmn : m < n)
    (hn : n < (cutoff H C).card) : enumeration H C m < enumeration H C n :=
  W29.finiteEnumeration_strictMono _ _ hmn hn

theorem lower_weight_earlier {H C n : ℕ} (hH : 0 < H)
    (hn : n < (cutoff H C).card) (a : Index H)
    (ha : weight a < weight (enumeration H C n)) :
    ∃ m < n, enumeration H C m = a := by
  obtain ⟨m, hm, hma⟩ := enumeration_complete hH a
    (ha.le.trans (enumeration_weight_le hH hn))
  refine ⟨m, ?_, hma⟩
  by_contra hmn
  have hnm : n ≤ m := by omega
  have hweight : weight (enumeration H C n) ≤ weight (enumeration H C m) := by
    rcases hnm.eq_or_lt with h | h
    · subst m; exact le_rfl
    · exact weight_monotone (enumeration_strictMono h hm).le
  rw [hma] at hweight
  exact (not_lt_of_ge hweight) ha

end WeightedTorusJets.W62



namespace SiegelZerosAwei.W30

open WeightedTorusJets

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [LinearOrder ι] {M : ℕ}

theorem greedy_ordered_earlier_span (row : ι → V) (s : Finset ι) (fallback : ι)
    (hcard : (W29.finiteSelection (K := K) row s fallback).card = M)
    (i : Fin M) {a : ι} (ha : a ∈ s)
    (hai : a < orderedIndex (W29.finiteSelection (K := K) row s fallback) hcard i) :
    row a ∈ Submodule.span K
      ((fun j => row (orderedIndex (W29.finiteSelection (K := K) row s fallback)
        hcard j)) '' Set.Iio i) := by
  apply mem_ordered_rows_earlier_span
  exact W29.lower_index_mem_selected_span row s fallback ha
    (W29.finiteSelection_subset row s fallback
      (orderedIndex_mem _ hcard i)) hai

theorem greedy_ordered_det_of_spanning (row : ι → Fin M → K)
    (s : Finset ι) (fallback : ι)
    (hspan : W29.rowSpan (K := K) row s = ⊤) :
    ∃ hcard : (W29.finiteSelection (K := K) row s fallback).card = M,
      Matrix.det (fun i j =>
        row (orderedIndex (W29.finiteSelection (K := K) row s fallback) hcard i) j) ≠ 0 := by
  apply ordered_rows_det_of_spanning
  · exact W29.finiteSelection_independent row s fallback
  · exact W29.finiteSelection_span_top row s fallback hspan

end SiegelZerosAwei.W30



namespace WeightedTorusJets.W62

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def selected (H C : ℕ) (row : Index H → V) : Finset (Index H) :=
  W29.finiteSelection (K := K) row (cutoff H C) (zeroIndex H)

theorem selected_independent (H C : ℕ) (row : Index H → V) :
    LinearIndepOn K row (selected (K := K) H C row : Set (Index H)) :=
  W29.finiteSelection_independent row _ _

theorem selected_span (H C : ℕ) (row : Index H → V) :
    W29.rowSpan (K := K) row (selected (K := K) H C row) =
      W29.rowSpan (K := K) row (cutoff H C) :=
  W29.finiteSelection_span row _ _

theorem selected_weight_le {H C : ℕ} (hH : 0 < H) (row : Index H → V)
    {a : Index H} (ha : a ∈ selected (K := K) H C row) : weight a ≤ C :=
  (mem_cutoff hH a).mp (W29.finiteSelection_subset row _ _ ha)

theorem lower_weight_mem_earlier_span {H C n : ℕ} (hH : 0 < H)
    (row : Index H → V) (hn : n < (cutoff H C).card) (a : Index H)
    (ha : weight a < weight (enumeration H C n)) :
    row a ∈ W29.rowSpan (K := K) row
      (W29.retained (K := K) row (enumeration H C) n) := by
  obtain ⟨m, hm, hma⟩ := lower_weight_earlier hH hn a ha
  rw [← hma]
  exact W29.earlier_row_mem_retained_span row _ hm

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem selected_card_of_spanning (H C : ℕ) (row : Index H → n → K)
    (hspan : W29.rowSpan (K := K) row (cutoff H C) = ⊤) :
    Fintype.card (selected (K := K) H C row) = Fintype.card n := by
  apply SiegelZerosAwei.W30.selected_card_eq row _ (selected_independent H C row)
  change W29.rowSpan (K := K) row (selected (K := K) H C row) = ⊤
  rw [selected_span, hspan]

theorem selected_det_ne_zero_of_spanning (H C : ℕ) (row : Index H → n → K)
    (hspan : W29.rowSpan (K := K) row (cutoff H C) = ⊤) :
    ∃ e : n ≃ selected (K := K) H C row,
      Matrix.det (fun i j => row (e i) j) ≠ 0 := by
  apply SiegelZerosAwei.W30.selected_equiv_det_ne_zero row _
    (selected_independent H C row)
  change W29.rowSpan (K := K) row (selected (K := K) H C row) = ⊤
  rw [selected_span, hspan]

theorem real_weight_eq {H : ℕ} (a : Index H) :
    SiegelZerosAwei.W31.weight (H : ℝ) a.coords = (weight a : ℝ) := by
  simp [SiegelZerosAwei.W31.weight, weight]

theorem coords_injective {H : ℕ} : Function.Injective (@Index.coords H) := by
  intro a b hab
  cases a
  cases b
  cases hab
  rfl

noncomputable def selectedCoords (H C : ℕ) (row : Index H → V) :
    Finset (Fin 3 → ℕ) := (selected (K := K) H C row).image Index.coords

theorem selectedCoords_card (H C : ℕ) (row : Index H → V) :
    (selectedCoords (K := K) H C row).card = (selected (K := K) H C row).card := by
  apply Finset.card_image_of_injective
  exact coords_injective

theorem selectedCoords_real_weight_le {H C : ℕ} (hH : 0 < H) (row : Index H → V)
    {a : Fin 3 → ℕ} (ha : a ∈ selectedCoords (K := K) H C row) :
    SiegelZerosAwei.W31.weight (H : ℝ) a ≤ (C : ℝ) := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [real_weight_eq]
  exact_mod_cast selected_weight_le hH row hb

theorem selectedCoords_short_sum {H C : ℕ} (hH : 0 < H) (row : Index H → V)
    {U : ℝ} (hC : (C : ℝ) ≤ 96 * (H : ℝ) ^ (2 / 3 : ℝ) * U) :
    (∑ a ∈ selectedCoords (K := K) H C row, ((a 1 : ℝ) + (a 2 : ℝ))) ≤
      96 * ((selected (K := K) H C row).card : ℝ) *
        (H : ℝ) ^ (-(1 / 3 : ℝ)) * U := by
  rw [← selectedCoords_card H C row]
  apply SiegelZerosAwei.W31.short_sum_le_96 (by exact_mod_cast hH)
  intro a ha
  exact (selectedCoords_real_weight_le hH row ha).trans hC

end WeightedTorusJets.W62


end SiegelZeros

end OAI
