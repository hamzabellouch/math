import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

theorem exists_strict_record_after (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (hlim : Tendsto a atTop (𝓝 0)) (N : ℕ) :
    ∃ k, N < k ∧ ∀ i < k, a k < a i := by
  classical
  obtain ⟨i, hi, hmin⟩ := (Finset.range (N + 1)).exists_min_image a (by simp)
  have hex : ∃ k, a k < a i := (hlim.eventually (gt_mem_nhds (hpos i))).exists
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra h
    have hk : Nat.find hex ∈ Finset.range (N + 1) := by
      simp only [Finset.mem_range]
      omega
    exact (not_lt_of_ge (hmin _ hk)) (Nat.find_spec hex)
  · intro j hj
    have hj' : a i ≤ a j := le_of_not_gt (Nat.find_min hex hj)
    exact lt_of_lt_of_le (Nat.find_spec hex) hj'

theorem infinite_strict_records (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (hlim : Tendsto a atTop (𝓝 0)) :
    Set.Infinite {k | ∀ i < k, a k < a i} := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨k, hk, hrec⟩ := exists_strict_record_after a hpos hlim N
  exact (not_lt_of_ge (hN hrec)) hk

theorem normalized_lengths_tendsto (L : ℕ → ℝ)
    (hpos : ∀ k, 0 < L k) (hbound : ∀ k, L k ≤ (2 : ℝ) ^ (3 * k)) :
    Tendsto (fun k => L k * (1 / 16 : ℝ) ^ k) atTop (𝓝 0) := by
  have hupper : ∀ k, L k * (1 / 16 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    calc
      L k * (1 / 16 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k) * (1 / 16 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (hbound k) (by positivity)
      _ = (1 / 2 : ℝ) ^ k := by
        rw [pow_mul, ← mul_pow]
        norm_num
  exact squeeze_zero (fun k => mul_nonneg (hpos k).le (by positivity)) hupper
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem record_scales (L : ℕ → ℝ) (hpos : ∀ k, 0 < L k)
    (hbound : ∀ k, L k ≤ (2 : ℝ) ^ (3 * k)) :
    ∀ N, ∃ k, N < k ∧ ∀ i ≤ k, L k ≤ (16 : ℝ) ^ (k - i) * L i := by
  intro N
  obtain ⟨k, hk, hrec⟩ := exists_strict_record_after
    (fun k => L k * (1 / 16 : ℝ) ^ k) (fun k => mul_pos (hpos k) (by positivity))
    (normalized_lengths_tendsto L hpos hbound) N
  refine ⟨k, hk, ?_⟩
  intro i hi
  have hcmp : L k * (1 / 16 : ℝ) ^ k ≤ L i * (1 / 16 : ℝ) ^ i := by
    rcases eq_or_lt_of_le hi with rfl | hi
    · exact le_refl _
    · exact le_of_lt (hrec i hi)
  have hp : (0 : ℝ) < 16 ^ k := by positivity
  have hmult := mul_le_mul_of_nonneg_right hcmp (le_of_lt hp)
  have hki : k = i + (k - i) := by omega
  have heq : (1 / 16 : ℝ) ^ i * 16 ^ k = 16 ^ (k - i) := by
    conv_lhs => rw [hki, pow_add]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hone : (1 / 16 : ℝ) ^ k * 16 ^ k = 1 := by
    rw [← mul_pow]; norm_num
  calc
    L k = (L k * (1 / 16 : ℝ) ^ k) * 16 ^ k := by rw [mul_assoc, hone, mul_one]
    _ ≤ (L i * (1 / 16 : ℝ) ^ i) * 16 ^ k := hmult
    _ = 16 ^ (k - i) * L i := by rw [mul_assoc, heq, mul_comm]

theorem record_scales_from (L : ℕ → ℝ) (k₀ : ℕ)
    (hpos : ∀ k, k₀ ≤ k → 0 < L k)
    (hbound : ∀ k, k₀ ≤ k → L k ≤ (2 : ℝ) ^ (3 * k)) :
    ∀ N, ∃ k, N < k ∧ k₀ ≤ k ∧
      ∀ j, j ≤ k - k₀ → (1 / 16 : ℝ) ^ j * L k ≤ L (k - j) := by
  classical
  intro N
  let L' : ℕ → ℝ := fun k => if k₀ ≤ k then L k else 1
  have hp : ∀ k, 0 < L' k := by
    intro k
    dsimp [L']
    split_ifs with h
    · exact hpos k h
    · norm_num
  have hb : ∀ k, L' k ≤ (2 : ℝ) ^ (3 * k) := by
    intro k
    dsimp [L']
    split_ifs with h
    · exact hbound k h
    · exact one_le_pow₀ (by norm_num)
  obtain ⟨k, hk, hrec⟩ := record_scales L' hp hb (max N k₀)
  have hk₀ : k₀ ≤ k := by omega
  refine ⟨k, by omega, hk₀, ?_⟩
  intro j hj
  have hjk : j ≤ k := by omega
  have hk' : k₀ ≤ k - j := by omega
  have hcomp := hrec (k - j) (Nat.sub_le _ _)
  have hsub : k - (k - j) = j := by omega
  simp only [L', ite_eq_left hk₀, ite_eq_left hk', hsub] at hcomp
  have hm := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ (1 / 16 : ℝ) ^ j by positivity)
  have hcancel : (1 / 16 : ℝ) ^ j * 16 ^ j = 1 := by
    rw [← mul_pow]; norm_num
  simpa only [← mul_assoc, hcancel, one_mul] using hm

end PlanarFPP

end OAI
