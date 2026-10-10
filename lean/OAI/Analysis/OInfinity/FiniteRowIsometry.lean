import OAI.Analysis.OInfinity.HalfFlipRecursion

namespace OAI

/-! # A finite isometry from a coisometric row to an incomplete row

The finite sum consists of all words of length at most `m` with an unused
isometry inserted between the source and target words. The recursion makes
its normalization and compression identities explicit. The target unit `q`
may be a proper corner; no commutation between the two rows is required.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

/-- The unnormalized sum `∑ |μ|≤m, s_μ r t_μ*`. -/
def finiteRowWordSum (s t : I → E) (r q : E) : ℕ → E
  | 0 => r * q
  | m + 1 => r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)

private lemma rowTransfer_star_mul (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (x y : E) :
    star (finiteCuntzTransfer t s x) * finiteCuntzTransfer t s y =
      ∑ i, t i * (star x * y) * star (t i) := by
  simp only [finiteCuntzTransfer, star_sum, star_mul, star_star,
    Finset.sum_mul, Finset.mul_sum]
  have hterm (i j : I) :
      (t i * (star x * star (s i))) * (s j * y * star (t j)) =
        if i = j then t i * (star x * y) * star (t i) else 0 := by
    calc
      _ = t i * star x * (star (s i) * s j) * y * star (t j) := by noncomm_ring
      _ = _ := by
        rw [hs]
        split_ifs with h
        · subst j; simp only [mul_one, mul_assoc]
        · simp only [mul_zero, zero_mul]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq I] in
private lemma rowRoot_star_transfer (s t : I → E) (r q x : E)
    (hr : ∀ i, star r * s i = 0) :
    star (r * q) * finiteCuntzTransfer t s x = 0 := by
  simp only [star_mul, finiteCuntzTransfer, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = star q * (star r * s i) * x * star (t i) := by noncomm_ring
    _ = 0 := by rw [hr, mul_zero, zero_mul, zero_mul]

private lemma rowSum_step_inner (s t : I → E) (r q x y : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) :
    star (r * q + finiteCuntzTransfer t s x) *
        (r * q + finiteCuntzTransfer t s y) =
      q + ∑ i, t i * (star x * y) * star (t i) := by
  have hroot : star (r * q) * (r * q) = q := by
    rw [star_mul, hqs]
    calc
      _ = q * (star r * r) * q := by noncomm_ring
      _ = q := by rw [hrr, mul_one, hq]
  have hleft := rowRoot_star_transfer s t r q y hr
  have hright : star (finiteCuntzTransfer t s x) * (r * q) = 0 := by
    simpa only [star_mul, star_star, star_zero] using
      congrArg star (rowRoot_star_transfer s t r q x hr)
  rw [star_add, add_mul, mul_add, mul_add, hroot, hleft, hright,
    rowTransfer_star_mul s t hs, add_zero, zero_add]

omit [DecidableEq I] in
private lemma rowTarget_scalar (t : I → E) (q : E)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (c : ℂ) :
    (∑ i, t i * (c • q) * star (t i)) = c • q := by
  simp only [mul_smul_comm, smul_mul_assoc, htq, ← Finset.smul_sum, ht]

/-- Equal-depth and consecutive-depth inner products have the same value. -/
lemma finiteRowWordSum_inner (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (m : ℕ) :
    star (finiteRowWordSum s t r q m) * finiteRowWordSum s t r q m =
        ((m : ℂ) + 1) • q ∧
      star (finiteRowWordSum s t r q m) * finiteRowWordSum s t r q (m + 1) =
        ((m : ℂ) + 1) • q := by
  induction m with
  | zero =>
    have hroot : star (r * q) * (r * q) = q := by
      rw [star_mul, hqs]
      calc
        _ = q * (star r * r) * q := by noncomm_ring
        _ = q := by rw [hrr, mul_one, hq]
    constructor
    · simpa only [finiteRowWordSum, Nat.cast_zero, zero_add, one_smul] using hroot
    · change star (r * q) * (r * q + finiteCuntzTransfer t s (r * q)) = _
      rw [mul_add, hroot, rowRoot_star_transfer s t r q _ hr, add_zero]
      simp only [Nat.cast_zero, zero_add, one_smul]
  | succ m ih =>
    constructor
    · change star (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)) *
        (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)) = _
      rw [rowSum_step_inner s t r q _ _ hq hqs hrr hr hs, ih.1,
        rowTarget_scalar t q htq ht]
      push_cast
      module
    · change star (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)) *
        (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q (m + 1))) = _
      rw [rowSum_step_inner s t r q _ _ hq hqs hrr hr hs, ih.2,
        rowTarget_scalar t q htq ht]
      push_cast
      module

lemma finiteRowWordSum_star_generator (s t : I → E) (r q : E)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (m : ℕ) (i : I) :
    star (finiteRowWordSum s t r q (m + 1)) * s i =
      t i * star (finiteRowWordSum s t r q m) := by
  change star (r * q + finiteCuntzTransfer t s (finiteRowWordSum s t r q m)) * s i = _
  rw [star_add, add_mul, star_mul, mul_assoc, hr, mul_zero, zero_add]
  simp only [finiteCuntzTransfer, star_sum, star_mul, star_star, Finset.sum_mul]
  have hterm (j : I) :
      (t j * (star (finiteRowWordSum s t r q m) * star (s j))) * s i =
        if j = i then t i * star (finiteRowWordSum s t r q m) else 0 := by
    calc
      _ = t j * star (finiteRowWordSum s t r q m) * (star (s j) * s i) := by noncomm_ring
      _ = _ := by rw [hs]; split_ifs with h <;> simp_all only [mul_one, mul_zero]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRowWordSum_compression (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (m : ℕ) (i : I) :
    star (finiteRowWordSum s t r q m) * s i * finiteRowWordSum s t r q m =
      (m : ℂ) • t i := by
  cases m with
  | zero =>
    change star (r * q) * s i * (r * q) = _
    rw [star_mul]
    calc
      _ = star q * (star r * s i) * (r * q) := by noncomm_ring
      _ = _ := by rw [hr, mul_zero, zero_mul]; simp only [Nat.cast_zero, zero_smul]
  | succ m =>
    rw [finiteRowWordSum_star_generator s t r q hr hs, mul_assoc,
      (finiteRowWordSum_inner s t r q hq hqs hrr hr hs htq ht m).2,
      mul_smul_comm, htq]
    norm_cast

lemma finiteRowWordSum_range_compression (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (m : ℕ) (i : I) :
    star (finiteRowWordSum s t r q m) * (s i * star (s i)) * finiteRowWordSum s t r q m =
      (m : ℂ) • (t i * star (t i)) := by
  cases m with
  | zero =>
    change star (r * q) * (s i * star (s i)) * (r * q) = _
    rw [star_mul]
    calc
      _ = q * (star r * s i) * star (s i) * r * q := by rw [hqs]; noncomm_ring
      _ = _ := by rw [hr, mul_zero, zero_mul, zero_mul, zero_mul]; simp only [Nat.cast_zero, zero_smul]
  | succ m =>
    have ha := congrArg star (finiteRowWordSum_star_generator s t r q hr hs m i)
    simp only [star_mul, star_star] at ha
    calc
      _ = (star (finiteRowWordSum s t r q (m + 1)) * s i) *
          (star (s i) * finiteRowWordSum s t r q (m + 1)) := by noncomm_ring
      _ = (t i * star (finiteRowWordSum s t r q m)) *
          (finiteRowWordSum s t r q m * star (t i)) := by
        rw [finiteRowWordSum_star_generator s t r q hr hs, ha]
      _ = t i * (star (finiteRowWordSum s t r q m) * finiteRowWordSum s t r q m) *
          star (t i) := by noncomm_ring
      _ = _ := by
        rw [(finiteRowWordSum_inner s t r q hq hqs hrr hr hs htq ht m).1,
          mul_smul_comm, smul_mul_assoc, htq]
        simp only [Nat.cast_add, Nat.cast_one]

/-- The normalized finite sum. -/
def finiteRowIsometry (s t : I → E) (r q : E) (m : ℕ) : E :=
  (((Real.sqrt ((m : ℝ) + 1))⁻¹ : ℝ) : ℂ) • finiteRowWordSum s t r q m

private lemma finiteRowScale_square (m : ℕ) :
    star ((((Real.sqrt ((m : ℝ) + 1))⁻¹ : ℝ) : ℂ)) *
        ((((Real.sqrt ((m : ℝ) + 1))⁻¹ : ℝ) : ℂ)) =
      ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv_rev,
    Real.mul_self_sqrt (by positivity)]

lemma finiteRowIsometry_gram (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (m : ℕ) :
    star (finiteRowIsometry s t r q m) * finiteRowIsometry s t r q m = q := by
  rw [finiteRowIsometry, star_smul, smul_mul_smul_comm, finiteRowScale_square,
    (finiteRowWordSum_inner s t r q hq hqs hrr hr hs htq ht m).1, smul_smul]
  have hc : ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ((m : ℂ) + 1) = 1 := by
    have hne : (m : ℝ) + 1 ≠ 0 := by positivity
    exact_mod_cast inv_mul_cancel₀ hne
  rw [hc, one_smul]

lemma finiteRowIsometry_compression (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (m : ℕ) (i : I) :
    star (finiteRowIsometry s t r q m) * s i * finiteRowIsometry s t r q m =
      (((m : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) • t i := by
  rw [finiteRowIsometry, star_smul, smul_mul_assoc, smul_mul_smul_comm,
    finiteRowScale_square, finiteRowWordSum_compression s t r q hq hqs hrr hr hs htq ht,
    smul_smul]
  congr 1
  push_cast
  ring

lemma finiteRowIsometry_range_compression (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q) (m : ℕ) (i : I) :
    star (finiteRowIsometry s t r q m) * (s i * star (s i)) * finiteRowIsometry s t r q m =
      (((m : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) • (t i * star (t i)) := by
  rw [finiteRowIsometry, star_smul, smul_mul_assoc, smul_mul_smul_comm,
    finiteRowScale_square, finiteRowWordSum_range_compression s t r q hq hqs hrr hr hs htq ht,
    smul_smul]
  congr 1
  push_cast
  ring

end WeakPureInfiniteness

end

end OAI
