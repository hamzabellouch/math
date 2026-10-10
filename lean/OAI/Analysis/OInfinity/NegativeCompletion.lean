import OAI.Analysis.OInfinity.NegativeCorner

namespace OAI

/-! # Finite leaf matching for the stabilized canonical row

The remaining projection of the negative-corner row is explicitly the
orthogonal sum of two copies of its unit. Matching the finite leaves and
using the concrete binary pair fills this projection without a
projection-classification assumption.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Match the common tail and each of finitely many range leaves. -/
def negativeLeafMatch {I : Type*} [Fintype I]
    (e r : E) (x y : I → E) : E := r * e + ∑ i, x i * star (y i)

lemma negativeLeafMatch_gram {I : Type*} [Fintype I] [DecidableEq I]
    (e r : E) (x y : I → E) (he : star e = e) (hee : e * e = e)
    (hr : star r * r = 1)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (hroot : ∀ i, star (x i) * r * e = 0) :
    star (negativeLeafMatch e r x y) * negativeLeafMatch e r x y =
      e + ∑ i, y i * star (y i) := by
  let T := ∑ i, x i * star (y i)
  have hrt : star (r * e) * T = 0 := by
    change star (r * e) * (∑ i, x i * star (y i)) = 0
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    have h := congrArg star (hroot i)
    simp only [star_mul, star_star, he, star_zero] at h
    calc
      _ = (e * (star r * x i)) * star (y i) := by rw [star_mul, he]; noncomm_ring
      _ = 0 := by rw [h, zero_mul]
  have htr : star T * (r * e) = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hrt
  have hrr : star (r * e) * (r * e) = e := by
    rw [star_mul, he]
    calc
      _ = e * (star r * r) * e := by noncomm_ring
      _ = e := by rw [hr, mul_one, hee]
  have htt : star T * T = ∑ i, y i * star (y i) := by
    simpa only [T, finiteCuntzTransfer, star_one, one_mul, mul_one] using
      finiteCuntzTransfer_star_mul y x hx 1
  change star (r * e + T) * (r * e + T) = _
  rw [star_add, add_mul, mul_add, mul_add, hrr, hrt, htr, htt, add_zero, zero_add]

lemma negativeLeafMatch_range {I : Type*} [Fintype I] [DecidableEq I]
    (e r : E) (x y : I → E) (he : star e = e) (hee : e * e = e)
    (hy : ∀ i j, star (y i) * y j = if i = j then 1 else 0)
    (hey : ∀ i, e * y i = 0) :
    negativeLeafMatch e r x y * star (negativeLeafMatch e r x y) =
      r * e * star r + ∑ i, x i * star (x i) := by
  let T := ∑ i, x i * star (y i)
  have hT : star T = finiteCuntzTransfer x y 1 := by
    simp only [T, finiteCuntzTransfer, star_sum, star_mul, star_star, mul_one]
  have hrt : (r * e) * star T = 0 := by
    rw [hT]
    change (r * e) * (∑ i, y i * 1 * star (x i)) = 0
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    calc
      _ = r * (e * y i) * star (x i) := by noncomm_ring
      _ = 0 := by rw [hey, mul_zero, zero_mul]
  have htr : T * star (r * e) = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hrt
  have hrr : (r * e) * star (r * e) = r * e * star r := by
    rw [star_mul, he]
    calc
      _ = r * (e * e) * star r := by noncomm_ring
      _ = _ := by rw [hee]
  have htt : T * star T = ∑ i, x i * star (x i) := by
    have h := finiteCuntzTransfer_star_mul x y hy 1
    rw [← hT, star_star] at h
    simpa only [star_one, one_mul, mul_one] using h
  change (r * e + T) * star (r * e + T) = _
  rw [star_add, add_mul, mul_add, mul_add, hrr, hrt, htr, htt, add_zero, zero_add]

lemma negativeLeafMatch_cross {I : Type*} [Fintype I]
    (e r R : E) (x X y : I → E) (he : star e = e)
    (hrr : e * star r * R * e = 0)
    (hrX : ∀ i, e * star r * X i = 0)
    (hxr : ∀ i, star (x i) * R * e = 0)
    (hxX : ∀ i j, star (x i) * X j = 0) :
    star (negativeLeafMatch e r x y) * negativeLeafMatch e R X y = 0 := by
  simp only [negativeLeafMatch, star_add, star_mul, he, star_sum, star_star,
    add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  have hroot : (e * star r) * (R * e) = 0 := by simpa only [mul_assoc] using hrr
  have hleft (i : I) : e * star r * (X i * star (y i)) = 0 := by
    rw [← mul_assoc, hrX, zero_mul]
  have hright (i : I) : (y i * star (x i)) * (R * e) = 0 := by
    calc
      _ = y i * (star (x i) * R * e) := by noncomm_ring
      _ = 0 := by rw [hxr, mul_zero]
  have hboth (i j : I) : (y i * star (x i)) * (X j * star (y j)) = 0 := by
    calc
      _ = y i * (star (x i) * X j) * star (y j) := by noncomm_ring
      _ = 0 := by rw [hxX, mul_zero, zero_mul]
  simp only [hroot, hleft, hright, hboth, Finset.sum_const_zero, add_zero]

/-- The first half of the matched range leaves. -/
def negativeLeftLeaf (s : ℕ → E) (n : ℕ) : Fin (n + 1) → E :=
  Fin.cases (s 1 * s n) (fun i => s (i + 2) * s 0)

/-- The second half of the matched range leaves. -/
def negativeRightLeaf (s : ℕ → E) (n : ℕ) : Fin (n + 1) → E :=
  Fin.cases (s 1 * s (n + 1)) (fun i => s (i + 2) * s 1)

private lemma twoLetter_gram (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (a b c d : ℕ) :
    star (s a * s b) * (s c * s d) =
      if a = c ∧ b = d then 1 else 0 := by
  rw [star_mul]
  calc
    _ = star (s b) * (star (s a) * s c) * s d := by noncomm_ring
    _ = _ := by rw [hs]; split_ifs <;> simp_all

lemma negativeLeftLeaf_gram (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    ∀ i j, star (negativeLeftLeaf s n i) * negativeLeftLeaf s n j =
      if i = j then 1 else 0 := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [negativeLeftLeaf, Fin.cases_zero, twoLetter_gram s hs, and_self, ite_true]
  · simp only [negativeLeftLeaf, Fin.cases_zero, Fin.cases_succ, twoLetter_gram s hs,
      show ¬1 = (j : ℕ) + 2 by omega, false_and, (Fin.succ_ne_zero j).symm, ite_false]
  · simp only [negativeLeftLeaf, Fin.cases_zero, Fin.cases_succ, twoLetter_gram s hs,
      show ¬(i : ℕ) + 2 = 1 by omega, false_and, Fin.succ_ne_zero, ite_false]
  · simp only [negativeLeftLeaf, Fin.cases_succ, twoLetter_gram s hs, and_true,
      Nat.add_right_cancel_iff, Fin.ext_iff, Fin.val_succ]

lemma negativeRightLeaf_gram (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    ∀ i j, star (negativeRightLeaf s n i) * negativeRightLeaf s n j =
      if i = j then 1 else 0 := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [negativeRightLeaf, Fin.cases_zero, twoLetter_gram s hs, and_self, ite_true]
  · simp only [negativeRightLeaf, Fin.cases_zero, Fin.cases_succ, twoLetter_gram s hs,
      show ¬1 = (j : ℕ) + 2 by omega, false_and, (Fin.succ_ne_zero j).symm, ite_false]
  · simp only [negativeRightLeaf, Fin.cases_zero, Fin.cases_succ, twoLetter_gram s hs,
      show ¬(i : ℕ) + 2 = 1 by omega, false_and, Fin.succ_ne_zero, ite_false]
  · simp only [negativeRightLeaf, Fin.cases_succ, twoLetter_gram s hs, and_true,
      Nat.add_right_cancel_iff, Fin.ext_iff, Fin.val_succ]

lemma negativeLeaf_cross (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    ∀ i j, star (negativeLeftLeaf s n i) * negativeRightLeaf s n j = 0 := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [negativeLeftLeaf, negativeRightLeaf, Fin.cases_zero, twoLetter_gram s hs,
      show ¬n = n + 1 by omega, and_false, ite_false]
  · simp only [negativeLeftLeaf, negativeRightLeaf, Fin.cases_zero, Fin.cases_succ,
      twoLetter_gram s hs, show ¬1 = (j : ℕ) + 2 by omega, false_and, ite_false]
  · simp only [negativeLeftLeaf, negativeRightLeaf, Fin.cases_zero, Fin.cases_succ,
      twoLetter_gram s hs, show ¬(i : ℕ) + 2 = 1 by omega, false_and, ite_false]
  · simp only [negativeLeftLeaf, negativeRightLeaf, Fin.cases_succ, twoLetter_gram s hs,
      Nat.zero_ne_one, and_false, ite_false]

lemma negativeLeaf_tail_support (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    ∀ i, canonicalTailProjection s (n + 2) * negativeLeftLeaf s n i = 0 ∧
      canonicalTailProjection s (n + 2) * negativeRightLeaf s n i = 0 ∧
      star (negativeLeftLeaf s n i) * s 1 * canonicalTailProjection s (n + 2) = 0 ∧
      star (negativeRightLeaf s n i) * s 1 * canonicalTailProjection s (n + 2) = 0 := by
  have he (j : ℕ) (hj : j < n + 2) : canonicalTailProjection s (n + 2) * s j = 0 := by
    rw [canonicalTailProjection_mul_generator s hs, ite_eq_left hj]
  have hes (j : ℕ) (hj : j < n + 2) : star (s j) * canonicalTailProjection s (n + 2) = 0 := by
    rw [canonicalTailProjection_generator_star s hs, ite_eq_left hj]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change _ * (s 1 * s n) = 0 ∧ _ * (s 1 * s (n + 1)) = 0 ∧
      star (s 1 * s n) * s 1 * _ = 0 ∧ star (s 1 * s (n + 1)) * s 1 * _ = 0
    have h1 : star (s 1) * s 1 = 1 := by simpa only [ite_true] using hs 1 1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← mul_assoc, he 1 (by omega), zero_mul]
    · rw [← mul_assoc, he 1 (by omega), zero_mul]
    · rw [star_mul, mul_assoc (star (s n)), h1, mul_one, hes n (by omega)]
    · rw [star_mul, mul_assoc (star (s (n + 1))), h1, mul_one, hes (n + 1) (by omega)]
  · change _ * (s (j + 2) * s 0) = 0 ∧ _ * (s (j + 2) * s 1) = 0 ∧
      star (s (j + 2) * s 0) * s 1 * _ = 0 ∧ star (s (j + 2) * s 1) * s 1 * _ = 0
    have hj : (j : ℕ) + 2 < n + 2 := by omega
    have hcross : star (s (j + 2)) * s 1 = 0 := by rw [hs, ite_eq_right (by omega)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← mul_assoc, he _ hj, zero_mul]
    · rw [← mul_assoc, he _ hj, zero_mul]
    · rw [star_mul, mul_assoc (star (s 0)), hcross, mul_zero, zero_mul]
    · rw [star_mul, mul_assoc (star (s 1)), hcross, mul_zero, zero_mul]

/-- The two finite leaf maps each have the required unit `e₁`, and their
ranges are orthogonal. -/
lemma negativeLeafMatch_pair (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    let e := canonicalTailProjection s (n + 2)
    let y : Fin (n + 1) → E := fun i => s (i + 1)
    let a := negativeLeafMatch e (s 1) (negativeLeftLeaf s n) y
    let b := negativeLeafMatch e 1 (negativeRightLeaf s n) y
    star a * a = canonicalTailProjection s 1 ∧
      star b * b = canonicalTailProjection s 1 ∧ star a * b = 0 := by
  intro e y a b
  have he : star e = e := canonicalTailProjection_star s (n + 2)
  have hee : e * e = e := canonicalTailProjection_idempotent s hs (n + 2)
  have h1 : star (s 1) * s 1 = 1 := by simpa only [ite_true] using hs 1 1
  have hsource : e + ∑ i, y i * star (y i) = canonicalTailProjection s 1 := by
    simpa only [y, e, Nat.add_comm 1, Nat.add_assoc] using
      (canonicalTailProjection_add s 1 (n + 1)).symm
  refine ⟨?_, ?_, ?_⟩
  · exact (negativeLeafMatch_gram e (s 1) _ y he hee h1
      (negativeLeftLeaf_gram s hs n) (fun i => (negativeLeaf_tail_support s hs n i).2.2.1)).trans hsource
  · exact (negativeLeafMatch_gram e 1 _ y he hee (by simp)
      (negativeRightLeaf_gram s hs n) (fun i => by
        have h := congrArg star (negativeLeaf_tail_support s hs n i).2.1
        simpa only [star_mul, star_zero, e, canonicalTailProjection_star, mul_one] using h)).trans hsource
  · apply negativeLeafMatch_cross e (s 1) 1 _ _ y he
    · have h : star (s 1) * e = 0 := by
        rw [canonicalTailProjection_generator_star s hs, ite_eq_left (by omega)]
      rw [mul_one, mul_assoc, h, mul_zero]
    · intro i
      have h := congrArg star (negativeLeaf_tail_support s hs n i).2.2.2
      simpa only [star_mul, star_star, star_zero, e, canonicalTailProjection_star, mul_assoc] using h
    · intro i
      have h := congrArg star (negativeLeaf_tail_support s hs n i).1
      simpa only [star_mul, star_zero, e, canonicalTailProjection_star, mul_one] using h
    · exact negativeLeaf_cross s hs n

lemma negativeLeaf_residual (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    canonicalTailProjection s 1 -
        ∑ i : Fin n, canonicalNegativeRow s i * star (canonicalNegativeRow s i) =
      s 1 * canonicalTailProjection s (n + 2) * star (s 1) +
        canonicalTailProjection s (n + 2) +
        (∑ i, negativeLeftLeaf s n i * star (negativeLeftLeaf s n i)) +
        (∑ i, negativeRightLeaf s n i * star (negativeRightLeaf s n i)) := by
  let p := canonicalNegativeProjection s
  let e := canonicalTailProjection s (n + 2)
  have hp : p = e + ∑ i : Fin n, s (i + 2) * star (s (i + 2)) := by
    simpa only [p, canonicalNegativeProjection, e, Nat.add_comm 2] using canonicalTailProjection_add s 2 n
  have hpn : 1 - p = s 0 * star (s 0) + s 1 * star (s 1) := by
    simp only [p, canonicalNegativeProjection, canonicalTailProjection, Fin.sum_univ_two]
    abel
  have hn : canonicalTailProjection s n =
      e + s n * star (s n) + s (n + 1) * star (s (n + 1)) := by
    simpa only [e, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.add_zero, add_assoc] using canonicalTailProjection_add s n 2
  have htail : p - ∑ i : Fin n, s (i + 2) * p * star (s (i + 2)) =
      e + ∑ i : Fin n, s (i + 2) * (1 - p) * star (s (i + 2)) := by
    rw [hp]
    simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
    abel
  rw [canonicalNegativeRow_residual s hs]
  change s 1 * canonicalTailProjection s n * star (s 1) +
      (p - ∑ i : Fin n, s (i + 2) * p * star (s (i + 2))) = _
  rw [htail, hn, hpn]
  simp only [Fin.sum_univ_succ, negativeLeftLeaf, negativeRightLeaf, Fin.cases_zero,
    Fin.cases_succ, star_mul, mul_add, add_mul, Finset.sum_add_distrib, mul_assoc]
  abel

lemma negativeLeafMatch_range_sum (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    let e := canonicalTailProjection s (n + 2)
    let y : Fin (n + 1) → E := fun i => s (i + 1)
    let a := negativeLeafMatch e (s 1) (negativeLeftLeaf s n) y
    let b := negativeLeafMatch e 1 (negativeRightLeaf s n) y
    a * star a + b * star b = canonicalTailProjection s 1 -
      ∑ i : Fin n, canonicalNegativeRow s i * star (canonicalNegativeRow s i) := by
  intro e y a b
  have he : star e = e := canonicalTailProjection_star s (n + 2)
  have hee : e * e = e := canonicalTailProjection_idempotent s hs (n + 2)
  have hy (i j : Fin (n + 1)) : star (y i) * y j = if i = j then 1 else 0 := by
    simp only [y, hs, Nat.add_right_cancel_iff, Fin.ext_iff]
  have hey (i : Fin (n + 1)) : e * y i = 0 := by
    dsimp only [e, y]
    rw [canonicalTailProjection_mul_generator s hs, ite_eq_left (by omega)]
  change negativeLeafMatch e (s 1) _ y * star (negativeLeafMatch e (s 1) _ y) +
    negativeLeafMatch e 1 _ y * star (negativeLeafMatch e 1 _ y) = _
  rw [negativeLeafMatch_range e (s 1) _ y he hee hy hey,
    negativeLeafMatch_range e 1 _ y he hee hy hey, one_mul, star_one, mul_one,
    negativeLeaf_residual s hs n]
  dsimp only [e]
  abel

/-- Combine the two matched copies with the explicit coisometric pair. -/
lemma negativeMatchedPair_completion (q a b u v : E)
    (hq : star q = q) (hqq : q * q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (huu : star u * u = q) (hvv : star v * v = q) (huv : star u * v = 0)
    (huvs : u * star u + v * star v = q) :
    star (a * star u + b * star v) * (a * star u + b * star v) = q ∧
      (a * star u + b * star v) * star (a * star u + b * star v) =
        a * star a + b * star b := by
  have haq := relativeIsometry_mul_support a q haa hq hqq
  have hbq := relativeIsometry_mul_support b q hbb hq hqq
  have huq := relativeIsometry_mul_support u q huu hq hqq
  have hvq := relativeIsometry_mul_support v q hvv hq hqq
  have hba : star b * a = 0 := by simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hvu : star v * u = 0 := by simpa only [star_mul, star_star, star_zero] using congrArg star huv
  constructor
  · calc
      _ = u * (star a * a) * star u + u * (star a * b) * star v +
          v * (star b * a) * star u + v * (star b * b) * star v := by
        simp only [star_add, star_mul, star_star]; noncomm_ring
      _ = q := by simp only [haa, hbb, hab, hba, mul_zero, zero_mul, add_zero, huq, hvq, huvs]
  · calc
      _ = a * (star u * u) * star a + a * (star u * v) * star b +
          b * (star v * u) * star a + b * (star v * v) * star b := by
        simp only [star_add, star_mul, star_star]; noncomm_ring
      _ = _ := by simp only [huu, hvv, huv, hvu, mul_zero, zero_mul, add_zero, haq, hbq]

/-- An actual relative isometry fills the full finite residual of the
stabilized canonical row, with no classification premise. -/
lemma exists_canonicalNegative_completion [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    ∃ c : E, star c * c = canonicalTailProjection s 1 ∧
      c * star c = canonicalTailProjection s 1 -
        ∑ i : Fin n, canonicalNegativeRow s i * star (canonicalNegativeRow s i) := by
  let q := canonicalTailProjection s 1
  have hq : star q = q := canonicalTailProjection_star s 1
  have hqq : q * q = q := canonicalTailProjection_idempotent s hs 1
  obtain ⟨u, v, w, _hw, _hu, _hv, _hweq, huu, hvv, huv, huvs⟩ :=
    exists_zero_corner_cuntz_pair (s 0) (s 1) (s 2)
      (by simpa only [ite_true] using hs 0 0)
      (by simpa only [ite_true] using hs 1 1)
      (by simpa only [ite_true] using hs 2 2)
      (by simpa using hs 0 1) (by simpa using hs 0 2) (by simpa using hs 1 2)
  have hqeq : 1 - s 0 * star (s 0) = q := by
    simp only [q, canonicalTailProjection, Fin.sum_univ_one, Fin.val_zero]
  rw [hqeq] at huu hvv huvs
  let e := canonicalTailProjection s (n + 2)
  let y : Fin (n + 1) → E := fun i => s (i + 1)
  let a := negativeLeafMatch e (s 1) (negativeLeftLeaf s n) y
  let b := negativeLeafMatch e 1 (negativeRightLeaf s n) y
  obtain ⟨haa, hbb, hab⟩ := negativeLeafMatch_pair s hs n
  have hpair := negativeMatchedPair_completion q a b u v hq hqq haa hbb hab huu hvv huv huvs
  refine ⟨a * star u + b * star v, hpair.1, ?_⟩
  exact hpair.2.trans (negativeLeafMatch_range_sum s hs n)

/-- Append one explicit range filler while retaining every prescribed
finite stabilized generator exactly. -/
lemma exists_canonicalNegative_full_row [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) :
    ∃ r : Fin (n + 1) → E,
      (∀ i : Fin n, r i.succ = canonicalNegativeRow s i) ∧
      (∀ i j, star (r i) * r j = if i = j then canonicalTailProjection s 1 else 0) ∧
      (∑ i, r i * star (r i)) = canonicalTailProjection s 1 := by
  let q := canonicalTailProjection s 1
  let z : Fin n → E := fun i => canonicalNegativeRow s i
  obtain ⟨c, hc, hcr⟩ := exists_canonicalNegative_completion s hs n
  change star c * c = q at hc
  let r : Fin (n + 1) → E := Fin.cases c z
  have hq : star q = q := canonicalTailProjection_star s 1
  have hqq : q * q = q := canonicalTailProjection_idempotent s hs 1
  have hcq : c * q = c := relativeIsometry_mul_support c q hc hq hqq
  have hz (i j : Fin n) : star (z i) * z j = if i = j then q else 0 := by
    simpa only [z, q, Fin.ext_iff] using canonicalNegativeRow_gram s hs i j
  have hzl (i : Fin n) : q * z i = z i := (canonicalNegativeRow_support s hs i).1
  have hzr (i : Fin n) : z i * q = z i := (canonicalNegativeRow_support s hs i).2
  have hdz (i : Fin n) : (q - ∑ j, z j * star (z j)) * z i = 0 := by
    rw [sub_mul, hzl, Finset.sum_mul]
    have hterm (j : Fin n) : z j * star (z j) * z i = if j = i then z i else 0 := by
      rw [mul_assoc, hz]
      split_ifs with hji
      · subst j; exact hzr i
      · exact mul_zero _
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]
  have hzdc (i : Fin n) : star (z i) * (c * star c) = 0 := by
    have h := congrArg star (hdz i)
    simp only [star_mul, star_sub, star_sum, star_star, hq, star_zero] at h
    simpa only [hcr, z, q] using h
  have hzc (i : Fin n) : star (z i) * c = 0 := by
    calc
      _ = star (z i) * (c * q) := by rw [hcq]
      _ = star (z i) * (c * star c) * c := by rw [← hc]; noncomm_ring
      _ = 0 := by rw [hzdc, zero_mul]
  have hcz (i : Fin n) : star c * z i = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star (hzc i)
  refine ⟨r, (fun i => rfl), ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [r, Fin.cases_zero, ite_true] using hc
    · simpa only [r, Fin.cases_zero, Fin.cases_succ, (Fin.succ_ne_zero j).symm,
        ite_false] using hcz j
    · simpa only [r, Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero i,
        ite_false] using hzc i
    · simpa only [r, Fin.cases_succ, Fin.succ_inj] using hz i j
  · simp only [r, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    rw [hcr]
    dsimp only [z, q]
    abel

end WeakPureInfiniteness

end

end OAI
