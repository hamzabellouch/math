import OAI.NumberTheory.Ostmann.Tree.PartitionMatching
import OAI.NumberTheory.Ostmann.Tree.ComponentFactorial
import OAI.NumberTheory.Ostmann.Tree.PartitionProducts

namespace OAI

/-! # Uniform counting bound for paired leaf partitions -/

namespace Ostmann

open scoped BigOperators Classical

abbrev BadPartitionPair (r t : ℕ) :=
  {fg : (Fin r → Fin t) × (Fin r → Fin t) //
    Function.Surjective fg.1 ∧ Function.Surjective fg.2 ∧
    (∀ c, Fintype.card {l : Fin r // fg.1 l = c} =
      Fintype.card {l : Fin r // fg.2 l = c}) ∧ 4 * (r - t) ≤ r}

abbrev BadPartitionWitness (r : ℕ) := Σ t : Fin (r + 1), BadPartitionPair r t

abbrev BadPartitionWitness.Matching {r : ℕ} (w : BadPartitionWitness r) (m : ℕ) :=
  PartitionMatching (fun x : Fin r × Fin m => w.2.1.1 x.1)
    (fun x : Fin r × Fin m => w.2.1.2 x.1)

theorem card_badPartitionPair_le (r t : ℕ) :
    Fintype.card (BadPartitionPair r t) ≤ t ^ (2 * r) := by
  calc
    _ ≤ Fintype.card ((Fin r → Fin t) × (Fin r → Fin t)) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp [Fintype.card_prod, pow_mul, pow_two, mul_pow]

theorem card_badPartitionWitness_le (r : ℕ) :
    Fintype.card (BadPartitionWitness r) ≤ (r + 1) * r ^ (2 * r) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ t : Fin (r + 1), r ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro t _
      exact (card_badPartitionPair_le r t).trans
        (Nat.pow_le_pow_left (Nat.le_of_lt_succ t.isLt) _)
    _ = _ := by simp

noncomputable def badPartitionCost (r m : ℕ) : ℝ :=
  (m.factorial : ℝ) ^ r * Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4)

theorem badPartitionCost_nonneg (r m : ℕ) : 0 ≤ badPartitionCost r m := by
  unfold badPartitionCost
  positivity

theorem badPartition_matching_bound {r : ℕ} (hr : 1 ≤ r)
    (w : BadPartitionWitness r) (m : ℕ) :
    (Fintype.card (w.Matching m) : ℝ) ≤ badPartitionCost r m := by
  let a : Fin w.1 → ℕ := fun c => Fintype.card {l : Fin r // w.2.1.1 l = c}
  have ha (c : Fin w.1) : 1 ≤ a c := by
    obtain ⟨l, hl⟩ := w.2.2.1 c
    exact Fintype.card_pos_iff.mpr ⟨⟨l, hl⟩⟩
  have hs : ∑ c, a c = r := by
    simpa only [Fintype.card_fin] using sum_card_partition w.2.1.1
  have hc : (Fintype.card (w.Matching m) : ℝ) ≤
      ∏ c, ((a c * m).factorial : ℝ) := by
    have hbal := fun c => w.2.2.2.2.1 c
    have h := card_slotMatching_le w.2.1.1 w.2.1.2 m
      (fun c => by simpa only [Fintype.card_eq_nat_card] using hbal c)
    have hnat : Fintype.card (w.Matching m) ≤ ∏ c, (a c * m).factorial := by
      simpa only [a, Fintype.card_eq_nat_card] using h
    exact_mod_cast hnat
  have ht : (w.1 : ℕ) ≤ r := Nat.le_of_lt_succ w.1.isLt
  have hd : 4 * ((r : ℝ) - (w.1 : ℕ)) ≤ r := by
    have h := w.2.2.2.2.2
    have h' : (4 : ℝ) * ((r - (w.1 : ℕ) : ℕ) : ℝ) ≤ r := by exact_mod_cast h
    simpa only [Nat.cast_sub ht] using h'
  have hl : 0 ≤ Real.log (r : ℝ) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ r by exact_mod_cast hr)
    linarith
  apply hc.trans
  apply (component_factorial_product_bound a r m ha hs).trans
  unfold badPartitionCost
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simp only [Fintype.card_fin]
  have hh := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (show (0 : ℝ) ≤ m by positivity) hl)
  nlinarith

/-- Sum over every possible pair of component partitions. The prefactor
depends only on r, and not on the number m of slots at a leaf. -/
theorem badPartition_total_bound {r : ℕ} (hr : 1 ≤ r) (m : ℕ) :
    (Fintype.card (Σ w : BadPartitionWitness r, w.Matching m) : ℝ) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) * badPartitionCost r m := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _w : BadPartitionWitness r, badPartitionCost r m :=
      Finset.sum_le_sum fun w _ => badPartition_matching_bound hr w m
    _ = (Fintype.card (BadPartitionWitness r) : ℝ) * badPartitionCost r m := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_badPartitionWitness_le r) (badPartitionCost_nonneg r m)

end Ostmann

end OAI
