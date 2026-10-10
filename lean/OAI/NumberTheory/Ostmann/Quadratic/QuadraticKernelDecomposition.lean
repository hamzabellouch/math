import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedSquarefreeRange

namespace OAI

/-! # Actual signed squarefree kernels of nonzero affine values -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_signed_squarefree_decomposition (x : ℤ) (hx : x ≠ 0) :
    ∃ (u : ℤ) (t : ℕ), u ≠ 0 ∧ 0 < t ∧ Squarefree u.natAbs ∧
      u * (t : ℤ) ^ 2 = x := by
  obtain ⟨a, t, ha, ht, heq, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hx)
  have heqZ : (a : ℤ) * (t : ℤ) ^ 2 = |x| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (mul_comm a (t ^ 2)).trans heq
  rcases le_total 0 x with hp | hn
  · refine ⟨a, t, by exact_mod_cast ha.ne', ht, by simpa, ?_⟩
    simpa [abs_of_nonneg hp] using heqZ
  · refine ⟨-(a : ℤ), t, neg_ne_zero.mpr (by exact_mod_cast ha.ne'), ht, by simpa, ?_⟩
    rw [abs_of_nonpos hn] at heqZ
    linear_combination -heqZ

theorem signed_kernel_mem_range {M : ℕ} {u x : ℤ} {t : ℕ}
    (hu : u ≠ 0) (ht : 0 < t) (hsf : Squarefree u.natAbs)
    (heq : u * (t : ℤ) ^ 2 = x) (hbound : |x| ≤ M) :
    u ∈ signedSquarefreeRange M := by
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have huabs : 0 ≤ |u| := abs_nonneg _
  have hle : |u| ≤ |x| := by
    rw [← heq, abs_mul, abs_pow, abs_of_nonneg (by omega : (0 : ℤ) ≤ t)]
    have ht2 : (1 : ℤ) ≤ (t : ℤ) ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left ht2 huabs
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp (hle.trans hbound)), hu, hsf⟩

/-- The bound used by the large sieve follows directly from the original
endpoint interval and the common center. -/
theorem affine_kernel_mem_range {X m : ℕ} {h u x : ℤ} {t : ℕ}
    (hu : u ≠ 0) (ht : 0 < t) (hsf : Squarefree u.natAbs)
    (heq : u * (t : ℤ) ^ 2 = (m : ℤ) * x - h) (hx : |x| ≤ X) :
    u ∈ signedSquarefreeRange (m * X + h.natAbs) := by
  apply signed_kernel_mem_range hu ht hsf heq
  calc
    |(m : ℤ) * x - h| ≤ |(m : ℤ) * x| + |h| := abs_sub _ _
    _ ≤ (m : ℤ) * X + |h| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      gcongr
    _ = ((m * X + h.natAbs : ℕ) : ℤ) := by simp

end Ostmann

end OAI
