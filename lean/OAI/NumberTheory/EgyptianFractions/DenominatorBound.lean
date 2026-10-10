import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.PrefixGap
import OAI.NumberTheory.EgyptianFractions.PrefixGrowth

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

 theorem ordered_unit_tail_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k) :
    0 < 1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ∧
    1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ≤
      (k : ℚ) / n i := by
  let s : Finset (Fin k) := Finset.univ.filter (· < i)
  let t : Finset (Fin k) := Finset.univ.filter (i ≤ ·)
  have hsplit : (∑ j ∈ s, (1 : ℚ) / n j) + (∑ j ∈ t, (1 : ℚ) / n j) = 1 := by
    calc
      _ = ∑ j : Fin k, (1 : ℚ) / n j := by
        simpa [s, t, not_lt] using
          (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin k)))
            (p := fun j => j < i) (f := fun j => (1 : ℚ) / n j))
      _ = 1 := hsum
  have hrem : 1 - ∑ j ∈ s, (1 : ℚ) / n j = ∑ j ∈ t, (1 : ℚ) / n j := by
    linarith
  change 0 < 1 - ∑ j ∈ s, (1 : ℚ) / n j ∧ _
  rw [hrem]
  constructor
  · apply lt_of_lt_of_le (show 0 < (1 : ℚ) / n i from div_pos zero_lt_one (by exact_mod_cast hn i))
    apply Finset.single_le_sum (f := fun j => (1 : ℚ) / n j) (a := i)
    · intro j hj
      positivity
    · simp [t]
  · calc
      ∑ j ∈ t, (1 : ℚ) / n j ≤ ∑ _j ∈ t, (1 : ℚ) / n i := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn i
        · exact_mod_cast hmono (by simpa [t] using hj)
      _ = (t.card : ℚ) / n i := by simp [div_eq_mul_inv]
      _ ≤ (k : ℚ) / n i := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show t.card ≤ k from (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ.trans (Fintype.card_fin k)))
        · positivity

 theorem denominator_le_prefix_product {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k)
    (hgap : (1 : ℚ) / (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) ≤
      1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j) :
    n i ≤ k * ∏ j ∈ Finset.univ.filter (· < i), n j := by
  have hle := hgap.trans (ordered_unit_tail_bound n hn hmono hsum i).2
  have hp : (0 : ℚ) < (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => hn j)
  have hi : (0 : ℚ) < n i := by exact_mod_cast hn i
  have hcross := (div_le_div_iff₀ hp hi).mp hle
  norm_num only [one_mul] at hcross
  exact_mod_cast hcross

/-- The coordinate estimate only needs weak ordering, so it also applies to
expansions with repeated denominators. -/
theorem ordered_unit_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) :
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) := by
  let P : ℕ → ℕ := fun t => ∏ j ∈ Finset.univ.filter (fun j : Fin k => j.val < t), n j
  have hrec : ∀ i : Fin k, n i ≤ k * P i.val := by
    intro i
    apply denominator_le_prefix_product n hn hmono hsum i
    exact prefix_remainder_gap _ n (fun j _ => hn j)
      (ordered_unit_tail_bound n hn hmono hsum i).1
  have hzero : P 0 = 1 := by simp [P]
  have hstep : ∀ t < k, P (t + 1) ≤ k * (P t) ^ 2 := by
    intro t ht
    let i : Fin k := ⟨t, ht⟩
    have hs : Finset.univ.filter (fun j : Fin k => j.val < t + 1) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < t)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          have hne : j.val ≠ t := by
            intro he
            apply hji
            apply Fin.ext
            exact he
          omega
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self t
        · omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin k => j.val < t) := by
      simp [i]
    have heq : P (t + 1) = n i * P t := by
      simp only [P, hs, Finset.prod_insert hnot]
    calc
      P (t + 1) = n i * P t := heq
      _ ≤ (k * P t) * P t := Nat.mul_le_mul_right (P t) (hrec i)
      _ = k * (P t) ^ 2 := by ring
  intro i
  exact denominator_growth_bound k i.val (P i.val) (n i)
    (prefix_growth_bound k k P hzero hstep i.val i.isLt.le) (hrec i)

 theorem one_expansion_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : IsOneExpansion n) : ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) :=
  ordered_unit_denominator_bound n (fun i => hn.1 i) hn.2.1.monotone hn.2.2

end Problem337

end

end OAI
