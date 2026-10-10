import OAI.NumberTheory.TwoPoint.Bounds.IntegerLiouville

namespace OAI

/-! A literal retained edge coefficient after testing. The vertex masks
are ambient predicates, so the coefficient is independent of the block. -/

namespace TwoPointCorrelations

open scoped Classical

noncomputable def retainedLiouvilleScalar (g : ℤ → ℝ) (keep : ℤ → Prop) (n : ℤ) : ℂ :=
  if keep n then (g n : ℂ) * integerLiouville n else 0

noncomputable def retainedLiouvilleEdge (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra keep : ℤ → Prop) (h d q : ℕ) (n m : ℤ) : ℂ :=
  if keep n ∧ keep m ∧ q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧
    eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n ∧
    integerEdgeKeep Q u eligible g L K extra m then
      (u q * center n : ℝ) * integerLiouville n * integerLiouville m else 0

lemma retainedLiouvilleScalar_star (g : ℤ → ℝ) (keep : ℤ → Prop) (n : ℤ) :
    star (retainedLiouvilleScalar g keep n) = retainedLiouvilleScalar g keep n := by
  unfold retainedLiouvilleScalar
  split_ifs <;> simp [star_mul, star_integerLiouville, mul_comm]

theorem retainedLiouvilleEdge_test (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hg : ∀ z, g z ≠ 0) :
    star (retainedLiouvilleScalar g keep n) *
        (directedIntegerEdge Q u eligible g center L K extra h d q n m : ℂ) *
        retainedLiouvilleScalar g keep m =
      (L : ℂ) * retainedLiouvilleEdge Q u eligible g center L K extra keep h d q n m := by
  by_cases hn : keep n
  · by_cases hm : keep m
    · simp only [retainedLiouvilleScalar, ite_eq_left hn, ite_eq_left hm]
      rw [directedEdge_liouville_test Q u eligible g center L K extra h d q n m hg]
      simp only [retainedLiouvilleEdge, hn, hm, true_and]
      split_ifs <;> simp only [Complex.ofReal_mul, mul_zero]
      ring
    · simp [retainedLiouvilleScalar, retainedLiouvilleEdge, hm]
  · simp [retainedLiouvilleScalar, retainedLiouvilleEdge, hn]

end TwoPointCorrelations

end OAI
