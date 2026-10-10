import OAI.Analysis.OInfinity.ZeroCornerRows

namespace OAI

/-! # The explicit negative-corner stabilization of a canonical row

The row in `1 - s₀s₀*` is the transport of the direct sum of the
canonical row and its tail compression in `1 - s₀s₀* - s₁s₁*`.
All projections and row identities below are literal algebraic formulas.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The remaining projection after the first `n` canonical ranges. -/
def canonicalTailProjection (s : ℕ → E) (n : ℕ) : E :=
  1 - ∑ i : Fin n, s i * star (s i)

lemma canonicalTailProjection_zero (s : ℕ → E) : canonicalTailProjection s 0 = 1 := by
  simp [canonicalTailProjection]

lemma canonicalTailProjection_succ (s : ℕ → E) (n : ℕ) :
    canonicalTailProjection s (n + 1) =
      canonicalTailProjection s n - s n * star (s n) := by
  simp only [canonicalTailProjection, Fin.sum_univ_castSucc]
  abel

lemma canonicalTailProjection_add (s : ℕ → E) (n k : ℕ) :
    canonicalTailProjection s n = canonicalTailProjection s (n + k) +
      ∑ i : Fin k, s (n + i) * star (s (n + i)) := by
  induction k with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ k ih =>
    rw [Nat.add_succ, canonicalTailProjection_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    abel

lemma canonicalTailProjection_star (s : ℕ → E) (n : ℕ) :
    star (canonicalTailProjection s n) = canonicalTailProjection s n := by
  simp only [canonicalTailProjection, star_sub, star_one, star_sum, star_mul, star_star]

lemma canonicalTailProjection_mul_generator (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n j : ℕ) :
    canonicalTailProjection s n * s j = if j < n then 0 else s j := by
  induction n with
  | zero => simp only [canonicalTailProjection_zero, one_mul, Nat.not_lt_zero, ite_false]
  | succ n ih =>
    rw [canonicalTailProjection_succ, sub_mul, mul_assoc, hs, ih]
    by_cases hj : j < n
    · have hne : n ≠ j := by omega
      simp only [hj, hne, ite_false, ite_true, mul_zero, sub_zero,
        show j < n + 1 by omega]
    · by_cases he : n = j
      · subst j
        simp only [Nat.lt_irrefl, ite_false, ite_true, mul_one, sub_self, Nat.lt_succ_self]
      · simp only [hj, he, ite_false, mul_zero, sub_zero, show ¬j < n + 1 by omega]

lemma canonicalTailProjection_generator_star (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n j : ℕ) :
    star (s j) * canonicalTailProjection s n = if j < n then 0 else star (s j) := by
  have h := congrArg star (canonicalTailProjection_mul_generator s hs n j)
  by_cases hj : j < n
  · simpa only [star_mul, canonicalTailProjection_star, hj, ite_true, star_zero] using h
  · simpa only [star_mul, canonicalTailProjection_star, hj, ite_false] using h

lemma canonicalTailProjection_idempotent (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    canonicalTailProjection s n * canonicalTailProjection s n = canonicalTailProjection s n := by
  induction n with
  | zero => simp only [canonicalTailProjection_zero, one_mul]
  | succ n ih =>
    have hl : canonicalTailProjection s n * s n = s n := by
      simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator s hs n n
    have hr : star (s n) * canonicalTailProjection s n = star (s n) := by
      simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_generator_star s hs n n
    have he : (s n * star (s n)) * (s n * star (s n)) = s n * star (s n) := by
      calc
        _ = s n * (star (s n) * s n) * star (s n) := by noncomm_ring
        _ = _ := by rw [hs, ite_eq_left rfl, mul_one]
    rw [canonicalTailProjection_succ]
    have hl' : canonicalTailProjection s n * (s n * star (s n)) = s n * star (s n) := by
      rw [← mul_assoc, hl]
    have hr' : (s n * star (s n)) * canonicalTailProjection s n = s n * star (s n) := by
      rw [mul_assoc, hr]
    noncomm_ring [ih, hl', hr', he]


lemma canonicalTailProjection_ne_zero [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    canonicalTailProjection s n ≠ 0 := by
  intro hzero
  have h : s n = 0 := by
    have hh := canonicalTailProjection_mul_generator s hs n n
    simpa only [hzero, zero_mul, Nat.lt_irrefl, ite_false] using hh.symm
  apply one_ne_zero (α := E)
  calc
    (1 : E) = star (s n) * s n := by simpa only [ite_true] using (hs n n).symm
    _ = 0 := by rw [h, mul_zero]

/-- The negative-unit corner used in the direct-sum stabilization. -/
def canonicalNegativeProjection (s : ℕ → E) : E := canonicalTailProjection s 2

/-- Transport of `sᵢ ⊕ (sᵢ₊₂ p)` along the rectangular row `[s₁,p]`. -/
def canonicalNegativeRow (s : ℕ → E) (i : ℕ) : E :=
  s 1 * s i * star (s 1) + s (i + 2) * canonicalNegativeProjection s

lemma canonicalNegativeProjection_le_tail (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) :
    canonicalTailProjection s 1 * canonicalNegativeProjection s = canonicalNegativeProjection s ∧
    canonicalNegativeProjection s * canonicalTailProjection s 1 = canonicalNegativeProjection s := by
  have hq := canonicalTailProjection_idempotent s hs 1
  have hl : canonicalTailProjection s 1 * s 1 = s 1 := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator s hs 1 1
  have hr : star (s 1) * canonicalTailProjection s 1 = star (s 1) := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_generator_star s hs 1 1
  change canonicalTailProjection s 1 * canonicalTailProjection s 2 = canonicalTailProjection s 2 ∧
    canonicalTailProjection s 2 * canonicalTailProjection s 1 = canonicalTailProjection s 2
  rw [canonicalTailProjection_succ s 1]
  constructor
  · rw [mul_sub, hq, ← mul_assoc, hl]
  · rw [sub_mul, hq, mul_assoc, hr]

lemma canonicalNegativeRow_gram (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i j : ℕ) :
    star (canonicalNegativeRow s i) * canonicalNegativeRow s j =
      if i = j then canonicalTailProjection s 1 else 0 := by
  let p := canonicalNegativeProjection s
  have hp : star p = p := canonicalTailProjection_star s 2
  have hpp : p * p = p := canonicalTailProjection_idempotent s hs 2
  have h11 : star (s 1) * s 1 = 1 := by simpa only [ite_true] using hs 1 1
  have hi1 : star (s 1) * s (j + 2) = 0 := by rw [hs, ite_eq_right (by omega)]
  have hj1 : star (s (i + 2)) * s 1 = 0 := by rw [hs, ite_eq_right (by omega)]
  have hA : star (s 1 * s i * star (s 1)) * (s 1 * s j * star (s 1)) =
      s 1 * (star (s i) * s j) * star (s 1) := by
    simp only [star_mul, star_star]
    calc
      _ = s 1 * star (s i) * (star (s 1) * s 1) * s j * star (s 1) := by noncomm_ring
      _ = _ := by rw [h11, mul_one]; noncomm_ring
  have hAB : star (s 1 * s i * star (s 1)) * (s (j + 2) * p) = 0 := by
    simp only [star_mul, star_star]
    calc
      _ = s 1 * star (s i) * (star (s 1) * s (j + 2)) * p := by noncomm_ring
      _ = 0 := by rw [hi1, mul_zero, zero_mul]
  have hBA : star (s (i + 2) * p) * (s 1 * s j * star (s 1)) = 0 := by
    simp only [star_mul, hp]
    calc
      _ = p * (star (s (i + 2)) * s 1) * s j * star (s 1) := by noncomm_ring
      _ = 0 := by rw [hj1, mul_zero, zero_mul, zero_mul]
  have hB : star (s (i + 2) * p) * (s (j + 2) * p) =
      p * (star (s (i + 2)) * s (j + 2)) * p := by rw [star_mul, hp]; noncomm_ring
  change star (s 1 * s i * star (s 1) + s (i + 2) * p) *
    (s 1 * s j * star (s 1) + s (j + 2) * p) = _
  rw [star_add, add_mul, mul_add, mul_add, hA, hAB, hBA, hB, add_zero, zero_add,
    hs, hs]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_one, hpp]
    change s 1 * star (s 1) + canonicalTailProjection s 2 = canonicalTailProjection s 1
    rw [canonicalTailProjection_succ s 1]
    abel
  · have hij' : i + 2 ≠ j + 2 := by omega
    simp only [hij, hij', ite_false, mul_zero, zero_mul, add_zero]

lemma canonicalNegativeRow_support (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i : ℕ) :
    canonicalTailProjection s 1 * canonicalNegativeRow s i = canonicalNegativeRow s i ∧
    canonicalNegativeRow s i * canonicalTailProjection s 1 = canonicalNegativeRow s i := by
  have hq1 : canonicalTailProjection s 1 * s 1 = s 1 := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_mul_generator s hs 1 1
  have hq2 : canonicalTailProjection s 1 * s (i + 2) = s (i + 2) := by
    simpa only [show ¬i + 2 < 1 by omega, ite_false] using
      canonicalTailProjection_mul_generator s hs 1 (i + 2)
  have hsq : star (s 1) * canonicalTailProjection s 1 = star (s 1) := by
    simpa only [Nat.lt_irrefl, ite_false] using canonicalTailProjection_generator_star s hs 1 1
  obtain ⟨_, hpq⟩ := canonicalNegativeProjection_le_tail s hs
  constructor
  · simp only [canonicalNegativeRow, mul_add, ← mul_assoc, hq1, hq2]
  · simp only [canonicalNegativeRow, add_mul, mul_assoc, hsq, hpq]

lemma canonicalNegativeRow_range_term (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i : ℕ) :
    canonicalNegativeRow s i * star (canonicalNegativeRow s i) =
      s 1 * (s i * star (s i)) * star (s 1) +
        s (i + 2) * canonicalNegativeProjection s * star (s (i + 2)) := by
  let p := canonicalNegativeProjection s
  have hp : star p = p := canonicalTailProjection_star s 2
  have hpp : p * p = p := canonicalTailProjection_idempotent s hs 2
  have hpl : p * s 1 = 0 := by
    exact (canonicalTailProjection_mul_generator s hs 2 1).trans (ite_eq_left (by omega))
  have hpr : star (s 1) * p = 0 := by
    simpa only [star_mul, hp, star_zero] using congrArg star hpl
  have h11 : star (s 1) * s 1 = 1 := by simpa only [ite_true] using hs 1 1
  change (s 1 * s i * star (s 1) + s (i + 2) * p) *
    star (s 1 * s i * star (s 1) + s (i + 2) * p) = _
  simp only [star_add, star_mul, star_star, hp, add_mul, mul_add]
  have ha : (s 1 * s i * star (s 1)) * (s 1 * (star (s i) * star (s 1))) =
      s 1 * (s i * star (s i)) * star (s 1) := by
    calc
      _ = s 1 * s i * (star (s 1) * s 1) * star (s i) * star (s 1) := by noncomm_ring
      _ = _ := by rw [h11, mul_one]; noncomm_ring
  have hab : (s 1 * s i * star (s 1)) * (p * star (s (i + 2))) = 0 := by
    calc
      _ = s 1 * s i * (star (s 1) * p) * star (s (i + 2)) := by noncomm_ring
      _ = 0 := by rw [hpr, mul_zero, zero_mul]
  have hba : (s (i + 2) * p) * (s 1 * (star (s i) * star (s 1))) = 0 := by
    calc
      _ = s (i + 2) * (p * s 1) * star (s i) * star (s 1) := by noncomm_ring
      _ = 0 := by rw [hpl, mul_zero, zero_mul, zero_mul]
  have hb : (s (i + 2) * p) * (p * star (s (i + 2))) =
      s (i + 2) * p * star (s (i + 2)) := by
    calc
      _ = s (i + 2) * (p * p) * star (s (i + 2)) := by noncomm_ring
      _ = _ := by rw [hpp]
  rw [ha, hab, hba, hb, add_zero, zero_add]

lemma canonicalNegativeRow_residual (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    canonicalTailProjection s 1 -
        ∑ i : Fin n, canonicalNegativeRow s i * star (canonicalNegativeRow s i) =
      s 1 * canonicalTailProjection s n * star (s 1) +
        (canonicalNegativeProjection s -
          ∑ i : Fin n, s (i + 2) * canonicalNegativeProjection s * star (s (i + 2))) := by
  simp_rw [canonicalNegativeRow_range_term s hs]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  have hq : canonicalTailProjection s 1 = s 1 * star (s 1) + canonicalNegativeProjection s := by
    change canonicalTailProjection s 1 = s 1 * star (s 1) + canonicalTailProjection s 2
    rw [canonicalTailProjection_succ s 1]
    abel
  rw [hq]
  unfold canonicalTailProjection
  noncomm_ring

lemma canonicalNegativeRow_spare (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    let q := canonicalTailProjection s 1
    let r := s (n + 2) * q
    star r * r = q ∧ q * r = r ∧ r * q = r ∧
      ∀ i : Fin n, star (canonicalNegativeRow s i) * r = 0 := by
  intro q r
  have hq : star q = q := canonicalTailProjection_star s 1
  have hqq : q * q = q := canonicalTailProjection_idempotent s hs 1
  have hnr : star (s (n + 2)) * s (n + 2) = 1 := by simpa only [ite_true] using hs (n + 2) (n + 2)
  have hqr : q * s (n + 2) = s (n + 2) := by
    rw [canonicalTailProjection_mul_generator s hs, ite_eq_right (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change star (s (n + 2) * q) * (s (n + 2) * q) = q
    rw [star_mul, hq]
    calc
      _ = q * (star (s (n + 2)) * s (n + 2)) * q := by noncomm_ring
      _ = q := by rw [hnr, mul_one, hqq]
  · change q * (s (n + 2) * q) = _
    rw [← mul_assoc, hqr]
  · change (s (n + 2) * q) * q = _
    rw [mul_assoc, hqq]
  · intro i
    have h1 : star (s 1) * s (n + 2) = 0 := by rw [hs, ite_eq_right (by omega)]
    have hi : star (s (i + 2)) * s (n + 2) = 0 := by rw [hs, ite_eq_right (by have := i.isLt; omega)]
    change star (s 1 * s i * star (s 1) + s (i + 2) * canonicalNegativeProjection s) *
      (s (n + 2) * q) = 0
    simp only [star_add, star_mul, star_star, add_mul]
    calc
      _ = s 1 * star (s i) * (star (s 1) * s (n + 2)) * q +
          star (canonicalNegativeProjection s) * (star (s (i + 2)) * s (n + 2)) * q := by noncomm_ring
      _ = 0 := by rw [h1, hi]; simp only [mul_zero, zero_mul, add_zero]

lemma canonicalTailProjection_commutes (s : ℕ → E) (x : E)
    (hc : ∀ i, Commute (s i) x ∧ Commute (star (s i)) x) (n : ℕ) :
    Commute (canonicalTailProjection s n) x := by
  exact (Commute.one_left x).sub_left
    (Commute.sum_left _ _ _ fun i _ => (hc i).1.mul_left (hc i).2)

lemma canonicalNegativeRow_commutes (s : ℕ → E) (x : E)
    (hc : ∀ i, Commute (s i) x ∧ Commute (star (s i)) x) (i : ℕ) :
    Commute (canonicalNegativeRow s i) x := by
  exact (((hc 1).1.mul_left (hc i).1).mul_left (hc 1).2).add_left
    ((hc (i + 2)).1.mul_left (canonicalTailProjection_commutes s x hc 2))

end WeakPureInfiniteness

end

end OAI
