import OAI.NumberTheory.JointDickman.Amplification.ArithmeticAmplification

namespace OAI

/-! # Exact finite reindexing of the amplification divisor sum -/

namespace JointDickman
open Finset

/-- Reindex a divisibility condition by its quotient, retaining the exact
finite endpoint and allowing the harmless zero term. -/
theorem sum_divisors_reindex {M : Type*} [AddCommMonoid M]
    {a : ℕ} (ha : 0 < a) (N : ℕ) (F : ℕ → M) :
    (∑ n ∈ (range N).filter (fun n => a ∣ n), F n) =
      ∑ m ∈ (range N).filter (fun m => a*m < N), F (a*m) := by
  classical
  apply sum_bij (fun n _ => n/a)
  · intro n hn
    obtain ⟨hnN,hd⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    constructor
    · exact mem_range.mpr ((Nat.div_le_self n a).trans_lt (mem_range.mp hnN))
    · simpa only [Nat.mul_div_cancel' hd] using mem_range.mp hnN
  · intro n hn k hk hnk
    have hd := (mem_filter.mp hn).2
    have he := (mem_filter.mp hk).2
    calc
      n = a*(n/a) := (Nat.mul_div_cancel' hd).symm
      _ = a*(k/a) := by rw [hnk]
      _ = k := Nat.mul_div_cancel' he
  · intro m hm
    have ham := (mem_filter.mp hm).2
    refine ⟨a*m,mem_filter.mpr ⟨mem_range.mpr ham, dvd_mul_right a m⟩,?_⟩
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

/-- The same identity in indicator form, convenient inside coefficient sums. -/
theorem sum_dvd_ite_reindex {M : Type*} [AddCommMonoid M]
    {a : ℕ} (ha : 0 < a) (N : ℕ) (F : ℕ → M) :
    (∑ n ∈ range N, if a ∣ n then F n else 0) =
      ∑ m ∈ range N, if a*m < N then F (a*m) else 0 := by
  classical
  simpa only [sum_filter] using sum_divisors_reindex ha N F

end JointDickman

end OAI
