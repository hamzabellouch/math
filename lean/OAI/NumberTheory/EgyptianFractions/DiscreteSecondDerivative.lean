import OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative
import OAI.NumberTheory.EgyptianFractions.SeparatedIntervalCount
import OAI.NumberTheory.EgyptianFractions.MonotoneBlocks
import OAI.NumberTheory.EgyptianFractions.SecondDerivativeBudget

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Natural-indexed strict-neighborhood version of the separated sample bound. -/
theorem nat_separated_near_integer_card (d : ℕ → ℝ) (N : ℕ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → lam * ((j : ℝ) - i) ≤ d j - d i)
    (hrange : ∀ i < N, L ≤ d i ∧ d i ≤ U) :
    ((nearIntegerIndices d N β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  classical
  have h := separated_near_integer_card ((Finset.range N).image Int.ofNat)
    (fun i : ℤ => d i.toNat) lam β L U hlam hβ hLU
    (by
      intro i hi j hj hij
      rcases Finset.mem_image.mp hi with ⟨ii, hii, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨jj, hjj, rfl⟩
      simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast] using
        hsep ii (Finset.mem_range.mp hii) jj (Finset.mem_range.mp hjj)
          (Int.ofNat_le.mp (by simpa only [Int.ofNat_eq_natCast] using hij)))
    (by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨ii, hii, rfl⟩
      exact hrange ii (Finset.mem_range.mp hii))
  simp only [Finset.filter_image, Int.ofNat_eq_natCast, Int.toNat_natCast] at h
  rw [Finset.card_image_of_injective _ Int.ofNat_injective] at h
  have hsub : nearIntegerIndices d N β ⊆
      (Finset.range N).filter (fun i => ∃ q : ℤ, |d i - (q : ℝ)| ≤ β) := by
    intro i hi
    obtain ⟨hiN, q, hq⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiN, q, hq.le⟩
  exact (show ((nearIntegerIndices d N β).card : ℝ) ≤
      (((Finset.range N).filter (fun i => ∃ q : ℤ, |d i - (q : ℝ)| ≤ β)).card : ℝ) by
    exact_mod_cast Finset.card_le_card hsub).trans h

namespace ExponentialSum

/-- A strip cancellation bound needing increment information only for the
indices being summed; the final endpoint costs at most one. -/
theorem first_derivative_Ico_bound (f : ℕ → ℝ) (a b : ℕ) (β : ℝ) (q : ℤ)
    (hab : a ≤ b) (hβ : 0 < β)
    (hlo : ∀ j ∈ Finset.Ico a b, (q : ℝ) + β ≤ f (j + 1) - f j)
    (hhi : ∀ j ∈ Finset.Ico a b, f (j + 1) - f j ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio b)) :
    ‖∑ j ∈ Finset.Ico a b, phase (f j)‖ ≤ 2 / β + 1 := by
  by_cases heq : a = b
  · subst b
    simp only [Finset.Ico_self, Finset.sum_empty, norm_zero]
    positivity
  have hab' : a < b := lt_of_le_of_ne hab heq
  let n := b - a - 1
  have hn : n + 1 = b - a := by dsimp [n]; omega
  let g : ℕ → ℝ := fun i => f (a + i)
  have hinc (i : ℕ) : g (i + 1) - g i = f (a + i + 1) - f (a + i) := by
    simp only [g, Nat.add_assoc]
  have hbound := first_derivative_sum_bound_strip g n β q hβ
    (by
      intro i hi
      rw [hinc]
      apply hlo
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (by
      intro i hi
      rw [hinc]
      apply hhi
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (by
      intro i hi j hj hij
      change g (i + 1) - g i ≤ g (j + 1) - g j
      rw [hinc, hinc]
      have hi' : i ≤ n := hi
      have hj' : j ≤ n := hj
      exact hmono (by change a + i < b; omega) (by change a + j < b; omega) (Nat.add_le_add_left hij a))
  rw [Finset.sum_Ico_eq_sum_range, ← hn, Finset.sum_range_succ]
  exact (norm_add_le _ _).trans (add_le_add hbound (le_of_eq (phase_norm _)))

/-- A fully discrete second-derivative estimate from monotone separated phase
increments. The only analytic input is the proved first-derivative test. -/
theorem discrete_second_derivative_partition_bound (f : ℕ → ℝ) (N : ℕ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (hLU : L ≤ U)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ U) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) + (U - L + 2) * (2 / β + 1) := by
  apply norm_sum_le_near_integer_bound_local (fun j => f (j + 1) - f j) N hmono β L U hβ hLU hrange
    (fun j => phase (f j)) _ (2 / β + 1) (by positivity)
  · intro j hj
    exact le_of_eq (phase_norm _)
  · exact nat_separated_near_integer_card _ N lam β L U hlam hβ.le hLU hsep hrange
  · intro q hq a b hab hbN hstrip
    exact first_derivative_Ico_bound f a b β q hab hβ
      (fun j hj => (hstrip j hj).1) (fun j hj => (hstrip j hj).2)
      (by
        intro i hi j hj hij
        exact hmono (lt_of_lt_of_le hi hbN) (lt_of_lt_of_le hj hbN) hij)

/-- The square-root form used in the reciprocal-phase differencing argument. -/
theorem discrete_second_derivative_sqrt_bound (f : ℕ → ℝ) (N : ℕ)
    (lam A L : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ L + A * lam * N) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have h := discrete_second_derivative_partition_bound f N lam (Real.sqrt lam) L (L + A * lam * N)
    hlam (Real.sqrt_pos.mpr hlam) (le_add_of_nonneg_right (by positivity)) hmono hsep hrange
  have hb := second_derivative_partition_sqrt_budget A (N : ℝ) lam hA (Nat.cast_nonneg _) hlam hlam1
  exact h.trans (by simpa only [add_sub_cancel_left] using hb)

end ExponentialSum
end Problem337

end OAI
