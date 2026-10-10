import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient

namespace OAI

/-! # Exact grouping of the two independent child frequency sums -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRootedFrequencyTree_root (V : ℕ → ℕ) (n : ℕ) (s : ℤ)
    (a : MovingDescendantFrequencyIndex V n) :
    frequencyRoot n (movingRootedFrequencyTree V n s a) = s := by
  cases n <;> rfl

theorem scheduledFrequencyIndex_sum_split (V : ℕ → ℕ) (n : ℕ)
    (f : ScheduledFrequencyIndex V n → ℂ) :
    (∑ a, f a) = ∑ s : transferFrequencyRange (V n),
      ∑ b : MovingDescendantFrequencyIndex V n,
        f ((scheduledFrequencyRootEquiv V n).symm (s, b)) := by
  simpa only [Fintype.sum_prod_type] using
    ((scheduledFrequencyRootEquiv V n).symm.sum_comp f).symm

theorem scheduledFrequencyHistory_from_root (V : ℕ → ℕ) (n : ℕ)
    (s : transferFrequencyRange (V n)) (a : MovingDescendantFrequencyIndex V n) :
    scheduledFrequencyHistory V n ((scheduledFrequencyRootEquiv V n).symm (s, a)) =
      movingRootedFrequencyTree V n s.val a := by
  rw [scheduledFrequencyRootEquiv_history, Equiv.apply_symm_apply]

/-- The two histories are independent after their roots are fixed. No number
of histories occurs in this exact distributive identity. The child functions
may depend on both roots through the reconstructed pivot. -/
theorem scheduledFrequency_bilinear_sum (V : ℕ → ℕ) (n : ℕ)
    (W : ℤ → ℤ → ℂ)
    (L R : ℤ → ℤ → FrequencyTree ℤ n → ℂ) :
    (∑ l : ScheduledFrequencyIndex V n, ∑ r : ScheduledFrequencyIndex V n,
      W (frequencyRoot n (scheduledFrequencyHistory V n l))
          (frequencyRoot n (scheduledFrequencyHistory V n r)) *
        L (frequencyRoot n (scheduledFrequencyHistory V n l))
          (frequencyRoot n (scheduledFrequencyHistory V n r)) (scheduledFrequencyHistory V n l) *
        star (R (frequencyRoot n (scheduledFrequencyHistory V n l))
          (frequencyRoot n (scheduledFrequencyHistory V n r)) (scheduledFrequencyHistory V n r))) =
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        W v.val w.val *
          (∑ a : MovingDescendantFrequencyIndex V n,
            L v.val w.val (movingRootedFrequencyTree V n v.val a)) *
          star (∑ b : MovingDescendantFrequencyIndex V n,
            R v.val w.val (movingRootedFrequencyTree V n w.val b)) := by
  rw [scheduledFrequencyIndex_sum_split V n]
  simp_rw [scheduledFrequencyIndex_sum_split V n,
    scheduledFrequencyHistory_from_root, movingRootedFrequencyTree_root]
  simp only [star_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]

end Ostmann

end OAI
