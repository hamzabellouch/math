import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DenominatorArithmetic

lemma unit_den (n : ℕ) (hn : 0 < n) : ((1 : ℚ) / (n : ℚ)).den = n := by
  simpa only [one_div] using Rat.inv_natCast_den_of_pos hn

lemma sum_unit_den_dvd_prod {α : Type*} (s : Finset α) (n : α → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) :
    (∑ i ∈ s, (1 : ℚ) / (n i : ℚ)).den ∣ ∏ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    apply (Rat.add_den_dvd _ _).trans
    rw [unit_den _ (hn a (Finset.mem_insert_self _ _))]
    exact Nat.mul_dvd_mul_left _ (ih (fun i hi => hn i (Finset.mem_insert_of_mem hi)))

lemma one_div_den_le {q : ℚ} (hq : 0 < q) : (1 : ℚ) / q.den ≤ q := by
  have hn : (1 : ℤ) ≤ q.num := by have := Rat.num_pos.mpr hq; omega
  have hnq : (1 : ℚ) ≤ (q.num : ℚ) := by exact_mod_cast hn
  calc
    (1 : ℚ) / q.den ≤ (q.num : ℚ) / q.den := by
      exact div_le_div_of_nonneg_right hnq (by positivity)
    _ = q := Rat.num_div_den q

lemma one_div_prod_le_remainder {α : Type*} (s : Finset α) (n : α → ℕ)
    (hn : ∀ i ∈ s, 0 < n i)
    (hq : 0 < 1 - ∑ i ∈ s, (1 : ℚ) / (n i : ℚ)) :
    (1 : ℚ) / (∏ i ∈ s, n i : ℕ) ≤ 1 - ∑ i ∈ s, (1 : ℚ) / (n i : ℚ) := by
  let q : ℚ := 1 - ∑ i ∈ s, (1 : ℚ) / (n i : ℚ)
  have hdvd : q.den ∣ ∏ i ∈ s, n i := by
    dsimp [q]
    simpa only [Rat.ofNat_sub_den] using sum_unit_den_dvd_prod s n hn
  have hp : 0 < ∏ i ∈ s, n i := Finset.prod_pos hn
  have hden : q.den ≤ ∏ i ∈ s, n i := Nat.le_of_dvd hp hdvd
  calc
    (1 : ℚ) / (∏ i ∈ s, n i : ℕ) ≤ 1 / q.den := by
      apply one_div_le_one_div_of_le
      · exact_mod_cast q.pos
      · exact_mod_cast hden
    _ ≤ q := one_div_den_le hq

lemma denominator_le_length_mul_prefix {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = 1) (i : Fin k) :
    n i ≤ k * ∏ j ∈ Finset.Iio i, n j := by
  classical
  let t := Finset.univ \ Finset.Iio i
  have hti : i ∈ t := by simp [t]
  have htail : 1 - ∑ j ∈ Finset.Iio i, (1 : ℚ) / (n j : ℚ) =
      ∑ j ∈ t, (1 : ℚ) / (n j : ℚ) := by
    have heq := Finset.sum_sdiff (f := fun j => (1 : ℚ) / (n j : ℚ))
      (Finset.subset_univ (Finset.Iio i))
    rw [hsum] at heq
    dsimp [t]
    linarith
  have htailpos : 0 < ∑ j ∈ t, (1 : ℚ) / (n j : ℚ) := by
    apply Finset.sum_pos'
    · intro j hj
      positivity
    · exact ⟨i, hti, one_div_pos.mpr (by exact_mod_cast hn i)⟩
  have hlower := one_div_prod_le_remainder (Finset.Iio i) n
    (fun j _ => hn j) (htail ▸ htailpos)
  rw [htail] at hlower
  have hupper : (∑ j ∈ t, (1 : ℚ) / (n j : ℚ)) ≤ (k : ℚ) / (n i : ℚ) := by
    calc
      (∑ j ∈ t, (1 : ℚ) / (n j : ℚ)) ≤ ∑ _j ∈ t, (1 : ℚ) / (n i : ℚ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn i
        · apply Nat.cast_le.mpr
          apply hmono
          have : ¬ j < i := by simpa [t] using (Finset.mem_sdiff.mp hj).2
          exact le_of_not_gt this
      _ = (t.card : ℚ) / (n i : ℚ) := by simp [div_eq_mul_inv]
      _ ≤ (k : ℚ) / (n i : ℚ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show t.card ≤ k from (Finset.card_le_card (Finset.subset_univ t)).trans_eq (Finset.card_fin k))
        · positivity
  have hp : (0 : ℚ) < (∏ j ∈ Finset.Iio i, n j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j (_ : j ∈ Finset.Iio i) => hn j)
  have hi : (0 : ℚ) < n i := by exact_mod_cast hn i
  have h := (div_le_div_iff₀ hp hi).mp (hlower.trans hupper)
  norm_num only [one_mul] at h
  exact_mod_cast h

lemma sum_two_pow_Iio {k : ℕ} (i : Fin k) :
    (∑ j ∈ Finset.Iio i, 2 ^ j.val) = 2 ^ i.val - 1 := by
  calc
    (∑ j ∈ Finset.Iio i, 2 ^ j.val) = ∑ j ∈ Finset.range i.val, 2 ^ j := by
      apply Finset.sum_bij (fun j _ => j.val)
      · intro j hj
        simpa using hj
      · intro j hj l hl heq
        exact Fin.ext heq
      · intro j hj
        have hji : j < i.val := Finset.mem_range.mp hj
        refine ⟨⟨j, hji.trans i.isLt⟩, ?_, rfl⟩
        exact Finset.mem_Iio.mpr hji
      · intros
        rfl
    _ = 2 ^ i.val - 1 := by
      simpa using geom_sum_mul_of_one_le (show (1 : ℕ) ≤ 2 by decide) i.val

theorem ordered_unit_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = 1) :
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) := by
  have hbound : ∀ j : ℕ, ∀ hj : j < k, n ⟨j, hj⟩ ≤ k ^ (2 ^ j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      let i : Fin k := ⟨j, hj⟩
      have hprod : (∏ l ∈ Finset.Iio i, n l) ≤ ∏ l ∈ Finset.Iio i, k ^ (2 ^ l.val) := by
        apply Finset.prod_le_prod
        intro l hl
        have hli : l < i := Finset.mem_Iio.mp hl
        exact ih l.val hli l.isLt
      calc
        n ⟨j, hj⟩ ≤ k * ∏ l ∈ Finset.Iio i, n l :=
          denominator_le_length_mul_prefix n hn hmono hsum i
        _ ≤ k * ∏ l ∈ Finset.Iio i, k ^ (2 ^ l.val) := Nat.mul_le_mul_left k hprod
        _ = k ^ (2 ^ j) := by
          rw [Finset.prod_pow_eq_pow_sum, sum_two_pow_Iio]
          have he : 1 + (2 ^ j - 1) = 2 ^ j := by
            have : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
            omega
          simpa only [i, Nat.pow_add, Nat.pow_one] using congrArg (fun e => k ^ e) he
  intro i
  exact hbound i.val i.isLt

end Problem337.DenominatorArithmetic

end

end OAI
