import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Estimates.DistinctIndexSums
import OAI.NumberTheory.Catalan.Estimates.TwoAdicQuadratic

namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem cast_triangle_product (m : ℕ) :
    ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
  cases m with
  | zero => norm_num
  | succ m =>
    simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem distinct_indices_twice_sum_lower {ι : Type*} (s : Finset ι)
    (f : ι → ℕ) (hf : Set.InjOn f (s : Set ι)) (b : ℕ)
    (hb : ∀ i ∈ s, b ≤ f i) :
    2 * ((s.card : ℝ) * (b : ℝ)) + (s.card : ℝ) * ((s.card : ℝ) - 1) ≤
      2 * ∑ i ∈ s, (f i : ℝ) := by
  have hs : s.card * b + (∑ k ∈ Finset.range s.card, k) ≤ ∑ i ∈ s, f i := by
    rw [Finset.sum_range_id]
    exact distinct_indices_sum_lower_of_le s f hf b hb
  have hg := Finset.sum_range_id_mul_two s.card
  have hn : 2 * (s.card * b) + s.card * (s.card - 1) ≤ 2 * ∑ i ∈ s, f i := by
    omega
  have hr : 2 * ((s.card : ℝ) * (b : ℝ)) + ((s.card * (s.card - 1) : ℕ) : ℝ) ≤
      2 * ∑ i ∈ s, (f i : ℝ) := by
    exact_mod_cast hn
  rwa [cast_triangle_product] at hr

theorem twoAdic_exponent_lower {ι : Type*} (N : ℕ) (E B : Finset ι)
    (u j : ι → ℕ)
    (huE : Set.InjOn u (E : Set ι)) (huB : Set.InjOn u (B : Set ι))
    (hjE : Set.InjOn j (E : Set ι)) (hb : ∀ k ∈ E, b N ≤ j k)
    (hcard : E.card + B.card ≤ n N) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 - 2 * (n N : ℝ) ≤
      ((2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) -
          (H N : ℤ) * (E.card : ℤ) + (∑ k ∈ B, (u k : ℤ)) +
          (Cdegree N : ℤ) * ((n N : ℤ) - (E.card : ℤ) - (B.card : ℤ)) : ℤ) : ℝ) := by
  have hE := distinct_indices_twice_sum_lower E u huE 0 (by simp)
  have hB := distinct_indices_twice_sum_lower B u huB 0 (by simp)
  have hJ := distinct_indices_twice_sum_lower E j hjE (b N) hb
  simp only [Nat.cast_zero, mul_zero, zero_add] at hE hB
  have hm : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hml : (E.card : ℝ) + (B.card : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hcard
  have hq := twoAdicQuadratic_lower N (E.card : ℝ) (B.card : ℝ) hm hl hml
  push_cast
  nlinarith only [hE, hB, hJ, hq, hm, hl, hml]

end InternalCatalan



namespace InternalCatalan

open scoped BigOperators

theorem twoAdic_selector_exponent_lower (N : ℕ)
    (τ : Fin (n N) → Fin 3) (u j : Fin (n N) → ℕ)
    (huE : Set.InjOn u {k | τ k = 1})
    (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, b N ≤ j k) :
    -(505 / 4608 : ℝ) * (n N : ℝ) ^ 2 - 2 * (n N : ℝ) ≤
      ((∑ k : Fin (n N),
        if τ k = 0 then (Cdegree N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
        else (u k : ℤ) : ℤ) : ℝ) := by
  classical
  let E : Finset (Fin (n N)) := Finset.univ.filter (fun k => τ k = 1)
  let B : Finset (Fin (n N)) := Finset.univ.filter (fun k => τ k = 2)
  have huE' : Set.InjOn u (E : Set (Fin (n N))) := by
    intro x hx y hy hxy
    exact huE (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have huB' : Set.InjOn u (B : Set (Fin (n N))) := by
    intro x hx y hy hxy
    exact huB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have hdisj : Disjoint E B := by
    apply Finset.disjoint_left.mpr
    intro k hkE hkB
    have he : τ k = 1 := (Finset.mem_filter.mp hkE).2
    have hb' : τ k = 2 := (Finset.mem_filter.mp hkB).2
    have hn : (1 : Fin 3) = 2 := he.symm.trans hb'
    norm_num at hn
  have hcard : E.card + B.card ≤ n N := by
    have hc := Finset.card_le_card (Finset.subset_univ (E ∪ B))
    rw [Finset.card_union_of_disjoint hdisj] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have heach (k : Fin (n N)) :
      (if τ k = 0 then (Cdegree N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
        else (u k : ℤ)) =
      (Cdegree N : ℤ) +
        (if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ) - (Cdegree N : ℤ)
          else 0) +
        (if τ k = 2 then (u k : ℤ) - (Cdegree N : ℤ) else 0) := by
    by_cases h₀ : τ k = 0
    · simp [h₀]
    by_cases h₁ : τ k = 1
    · simp [h₁]
    have h₂ : τ k = 2 := by omega
    simp [h₂]
  have hsumE : (∑ k : Fin (n N),
      if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ) - (Cdegree N : ℤ)
        else 0) =
      ∑ k ∈ E, (2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ) - (Cdegree N : ℤ)) := by
    simp only [E, Finset.sum_filter]
  have hsumB : (∑ k : Fin (n N),
      if τ k = 2 then (u k : ℤ) - (Cdegree N : ℤ) else 0) =
      ∑ k ∈ B, ((u k : ℤ) - (Cdegree N : ℤ)) := by
    simp only [B, Finset.sum_filter]
  have hsumC : (∑ _ : Fin (n N), (Cdegree N : ℤ)) = (n N : ℤ) * (Cdegree N : ℤ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Int.nsmul_eq_mul]
  have hsum : (∑ k : Fin (n N),
      if τ k = 0 then (Cdegree N : ℤ)
      else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
      else (u k : ℤ)) =
      2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) -
        (H N : ℤ) * (E.card : ℤ) + (∑ k ∈ B, (u k : ℤ)) +
        (Cdegree N : ℤ) * ((n N : ℤ) - (E.card : ℤ) - (B.card : ℤ)) := by
    simp_rw [heach]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumE, hsumB, hsumC]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Int.nsmul_eq_mul]
    ring
  rw [hsum]
  exact twoAdic_exponent_lower N E B u j huE' huB'
    (fun _ _ _ _ h => hj h) (fun k _ => hb k) hcard

theorem twoAdic_selector_zpow_le (N : ℕ)
    (τ : Fin (n N) → Fin 3) (u j : Fin (n N) → ℕ)
    (huE : Set.InjOn u {k | τ k = 1})
    (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, b N ≤ j k) :
    (2 : ℝ) ^ (-(∑ k : Fin (n N),
        if τ k = 0 then (Cdegree N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H N : ℤ)
        else (u k : ℤ))) ≤
      (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  have h := twoAdic_selector_exponent_lower N τ u j huE huB hj hb
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  simp only [Int.cast_neg]
  linarith only [h]

end InternalCatalan

end OAI
