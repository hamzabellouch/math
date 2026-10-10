import OAI.Analysis.OInfinity.FiniteRowDefect

namespace OAI

/-! # Connected completion of the finite row isometry

A second unused source isometry is orthogonal to the entire finite sum.
When its range is the complement of the target corner, it is an actual
common spare for the two-swap completion. The complementary projection is
therefore the range of an explicit unit-source isometry.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma finiteRowWordSum_unused (s t : I → E) (r q z : E)
    (hzr : star z * r = 0) (hzs : ∀ i, star z * s i = 0) (m : ℕ) :
    star z * finiteRowWordSum s t r q m = 0 := by
  cases m with
  | zero => change star z * (r * q) = 0; rw [← mul_assoc, hzr, zero_mul]
  | succ m =>
    change star z * (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)) = 0
    rw [mul_add, ← mul_assoc (star z) r, hzr, zero_mul, zero_add]
    simp only [finiteCuntzTransfer, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    calc
      _ = (star z * s i) * finiteRowWordSum s t r q m * star (t i) := by noncomm_ring
      _ = 0 := by rw [hzs, zero_mul, zero_mul]

omit [DecidableEq I] in
lemma finiteRowIsometry_unused (s t : I → E) (r q z : E)
    (hzr : star z * r = 0) (hzs : ∀ i, star z * s i = 0) (m : ℕ) :
    star z * finiteRowIsometry s t r q m = 0 := by
  rw [finiteRowIsometry, mul_smul_comm, finiteRowWordSum_unused s t r q z hzr hzs,
    smul_zero]

omit [DecidableEq I] in
lemma finiteRowRange_unused (s t : I → E) (r q z : E)
    (hzr : star z * r = 0) (hzs : ∀ i, star z * s i = 0) (m : ℕ) :
    finiteRowRange s t r q m * z = 0 := by
  have h : star (finiteRowIsometry s t r q m) * z = 0 := by
    simpa only [star_mul, star_star, star_zero] using
      congrArg star (finiteRowIsometry_unused s t r q z hzr hzs m)
  rw [finiteRowRange, mul_assoc, h, mul_zero]

/-- The completion retains a literal complement isometry, not only a
K-theoretic relation between projections. -/
lemma exists_connected_finiteRowCompletion [Nontrivial E]
    (s t : I → E) (r q z : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q)
    (hz : star z * z = 1) (hzr : star z * r = 0)
    (hzs : ∀ i, star z * s i = 0) (hqz : q = 1 - z * star z) (m : ℕ) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) = partialIsometryCompletion z q (finiteRowIsometry s t r q m) ∧
      (u : E) * q = finiteRowIsometry s t r q m ∧
      star ((u : E) * z) * ((u : E) * z) = 1 ∧
      ((u : E) * z) * star ((u : E) * z) = 1 - finiteRowRange s t r q m := by
  let v := finiteRowIsometry s t r q m
  have hvg : star v * v = q := finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht m
  have hvq : v * q = v := relativeIsometry_mul_support v q hvg hqs hq
  have hvp : v * star v * v = v := by rw [mul_assoc, hvg, hvq]
  have hqz0 : q * z = 0 := by
    rw [hqz, sub_mul, one_mul, mul_assoc, hz, mul_one, sub_self]
  have hfz : (v * star v) * z = 0 := finiteRowRange_unused s t r q z hzr hzs m
  obtain ⟨u, hu, hueq, huv⟩ := exists_explicit_connected_unitary_extension v z hvp hz
    (by rw [hvg]; exact hqz0) hfz
  have huq : (u : E) * q = v := by simpa only [hvg] using huv
  have huqu : (u : E) * q * star (u : E) = v * star v := by
    calc
      _ = ((u : E) * q) * star ((u : E) * q) := by
        rw [star_mul, hqs]
        symm
        calc
          _ = (u : E) * (q * q) * star (u : E) := by noncomm_ring
          _ = _ := by rw [hq]
      _ = _ := by rw [huq]
  refine ⟨u, hu, ?_, huq, ?_, ?_⟩
  · simpa only [hvg] using hueq
  · rw [star_mul]
    calc
      _ = star z * (star (u : E) * (u : E)) * z := by noncomm_ring
      _ = 1 := by rw [u.property.1, mul_one, hz]
  · change ((u : E) * z) * star ((u : E) * z) = 1 - v * star v
    rw [star_mul]
    calc
      _ = (u : E) * (z * star z) * star (u : E) := by noncomm_ring
      _ = (u : E) * (1 - q) * star (u : E) := by rw [hqz]; congr 2; abel
      _ = 1 - v * star v := by
        rw [mul_sub, mul_one, sub_mul, u.property.2, huqu]

end WeakPureInfiniteness

end

end OAI
