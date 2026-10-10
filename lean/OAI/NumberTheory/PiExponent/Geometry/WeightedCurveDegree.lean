import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent.WeightedCurveDegree

noncomputable def integerOrder {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) : ℤ :=
  (v (x : K)).untop ((AddValuation.top_iff v).not.mpr x.ne_zero)

@[simp] theorem coe_integerOrder {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (integerOrder v x : WithTop ℤ) = v (x : K) := WithTop.coe_untop _ _

@[simp] theorem integerOrder_one {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : integerOrder v 1 = 0 := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_mul {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x * y) = integerOrder v x + integerOrder v y := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_pow {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) (n : ℕ) :
    integerOrder v (x ^ n) = n * integerOrder v x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, integerOrder_mul, ih]; push_cast; ring

@[simp] theorem integerOrder_prod {K ι : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (s : Finset ι) (x : ι → Kˣ) :
    integerOrder v (∏ i ∈ s, x i) = ∑ i ∈ s, integerOrder v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

theorem integerOrder_monomial {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ) (a : ι → ℕ) :
    integerOrder v (∏ i, x i ^ a i) = ∑ i, (a i : ℤ) * integerOrder v (x i) := by
  simp

noncomputable def weightedPole {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) : ℚ :=
  (Finset.univ : Finset (Option ι)).sup' Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -z j / w j))

theorem weightedPole_nonneg {ι : Type*} [Fintype ι] (w z : ι → ℚ) :
    0 ≤ weightedPole w z := by
  exact Finset.le_sup' (fun i : Option ι => i.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (none : Option ι))

theorem div_le_weightedPole {ι : Type*} [Fintype ι] (w z : ι → ℚ) (i : ι) :
    -z i / w i ≤ weightedPole w z := by
  exact Finset.le_sup' (fun o : Option ι => o.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (some i))

theorem monomial_pole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    -(∑ i, (a i : ℚ) * z i) ≤ R * weightedPole w z := by
  have hcoord (i : ι) : -z i ≤ w i * weightedPole w z := by
    have h := (div_le_iff₀ (hw i)).mp (div_le_weightedPole w z i)
    simpa [mul_comm] using h
  calc
    _ = ∑ i, (a i : ℚ) * (-z i) := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ i, (a i : ℚ) * (w i * weightedPole w z) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcoord i) (Nat.cast_nonneg _)
    _ = (∑ i, w i * (a i : ℚ)) * weightedPole w z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ R * weightedPole w z :=
      mul_le_mul_of_nonneg_right ha (weightedPole_nonneg w z)

theorem monomial_max_pole_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w z : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (_hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R) :
    monomials.sup' ⟨0, hzero⟩ (fun a => -(∑ i, (a i : ℚ) * z i)) =
      R * weightedPole w z := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    exact monomial_pole_le w z hw a (hbudget a ha)
  · obtain ⟨o, _, ho⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Option ι))) Finset.univ_nonempty
      (fun i => i.elim 0 (fun j => -z j / w j))
    change weightedPole w z = _ at ho
    rw [ho]
    cases o with
    | none =>
      simpa using Finset.le_sup' (fun a => -(∑ i, (a i : ℚ) * z i)) hzero
    | some i =>
      have hp := Finset.le_sup' (fun a => -(∑ j, (a j : ℚ) * z j)) (hpure i)
      have hs : (∑ j, (((Pi.single i (powers i) : ι → ℕ) j) : ℚ) * z j) = (powers i : ℚ) * z i := by
        simp [Pi.single_apply]
      rw [hs] at hp
      change R * (-z i / w i) ≤ _
      have he : R * (-z i / w i) = -(powers i : ℚ) * z i := by
        rw [← hpowers i]
        field_simp [ne_of_gt (hw i)]
      rw [he]
      simpa using hp

theorem valuation_monomial_max_pole_eq
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R) :
    monomials.sup' ⟨0, hzero⟩
        (fun a => -(integerOrder v (∏ i, x i ^ a i) : ℚ)) =
      R * weightedPole w (fun i => (integerOrder v (x i) : ℚ)) := by
  simpa only [integerOrder_monomial, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using
    monomial_max_pole_eq w (fun i => (integerOrder v (x i) : ℚ)) hw hR
      powers hpowers monomials hzero hpure hbudget

noncomputable def monomialPoleCoefficient
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) : ℤ :=
  monomials.sup' ⟨0, hzero⟩ (fun a => -integerOrder v (∏ i, x i ^ a i))

theorem monomialPoleCoefficient_nonneg
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    0 ≤ monomialPoleCoefficient v x monomials hzero := by
  have h := Finset.le_sup' (fun a => -integerOrder v (∏ i, x i ^ a i)) hzero
  simpa [monomialPoleCoefficient] using h

theorem monomialPoleCoefficient_eq
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R) :
    (monomialPoleCoefficient v x monomials hzero : ℚ) =
      R * weightedPole w (fun i => (integerOrder v (x i) : ℚ)) := by
  unfold monomialPoleCoefficient
  rw [Finset.apply_sup'_eq_sup'_comp ⟨0, hzero⟩ (fun n : ℤ => (n : ℚ))
    (by intro a b; exact_mod_cast (show max a b = max a b from rfl))]
  simpa only [Function.comp_def, Int.cast_neg] using
    valuation_monomial_max_pole_eq v x w hw hR powers hpowers monomials hzero hpure hbudget

theorem monomialPoleCoefficient_eq_zero
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hx : ∀ i, integerOrder v (x i) = 0) :
    monomialPoleCoefficient v x monomials hzero = 0 := by
  unfold monomialPoleCoefficient
  simp only [integerOrder_prod, integerOrder_pow, hx, mul_zero, Finset.sum_const_zero, neg_zero]
  exact Finset.sup'_const _ _

noncomputable def monomialPoleDivisor
    {K ι P : Type*} [Field K] [Fintype ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) : P →₀ ℤ :=
  Finsupp.onFinset support (fun p => monomialPoleCoefficient (v p) x monomials hzero)
    (by
      intro p hp
      by_contra hnot
      exact hp (monomialPoleCoefficient_eq_zero (v p) x monomials hzero (hsupport p hnot)))

@[simp] theorem monomialPoleDivisor_apply
    {K ι P : Type*} [Field K] [Fintype ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) (p : P) :
    monomialPoleDivisor v x monomials hzero support hsupport p =
      monomialPoleCoefficient (v p) x monomials hzero := by
  unfold monomialPoleDivisor
  exact Finsupp.onFinset_apply

theorem monomialPoleDivisor_effective
    {K ι P : Type*} [Field K] [Fintype ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) :
    0 ≤ monomialPoleDivisor v x monomials hzero support hsupport := by
  intro p
  exact monomialPoleCoefficient_nonneg (v p) x monomials hzero

theorem monomialPoleDivisor_degree_eq
    {K ι P : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) :
    ((monomialPoleDivisor v x monomials hzero support hsupport).sum (fun _ n => n) : ℚ) =
      R * ∑ p ∈ support, weightedPole w (fun i => (integerOrder (v p) (x i) : ℚ)) := by
  unfold monomialPoleDivisor
  rw [Finsupp.sum_onFinset _ _ _ _ (by intro p _; rfl)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact monomialPoleCoefficient_eq (v p) x w hw hR powers hpowers monomials hzero hpure hbudget

@[simp] theorem integerOrder_inv {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    integerOrder v x⁻¹ = -integerOrder v x := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_div {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x / y) = integerOrder v x - integerOrder v y := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

theorem mem_valuationSubring_iff_order_nonneg {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (x : K) ∈ v.toValuation.valuationSubring ↔ 0 ≤ integerOrder v x := by
  change (0 : WithTop ℤ) ≤ v (x : K) ↔ 0 ≤ integerOrder v x
  rw [← coe_integerOrder]
  exact WithTop.coe_le_coe

theorem exists_regular_monomial_chart
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    ∃ a ∈ monomials,
      integerOrder v (∏ i, x i ^ a i) = -monomialPoleCoefficient v x monomials hzero ∧
      (∀ b ∈ monomials,
        (((∏ i, x i ^ b i) / (∏ i, x i ^ a i) : Kˣ) : K) ∈
          v.toValuation.valuationSubring) ∧
      (((∏ i, x i ^ a i) / (∏ i, x i ^ a i) : Kˣ) : K) = 1 := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup' ⟨0, hzero⟩
    (fun a => -integerOrder v (∏ i, x i ^ a i))
  change monomialPoleCoefficient v x monomials hzero = _ at hmax
  refine ⟨a, ha, by linarith, ?_, ?_⟩
  · intro b hb
    apply (mem_valuationSubring_iff_order_nonneg v _).mpr
    rw [integerOrder_div]
    have h := Finset.le_sup' (fun a => -integerOrder v (∏ i, x i ^ a i)) hb
    change -integerOrder v (∏ i, x i ^ b i) ≤ monomialPoleCoefficient v x monomials hzero at h
    linarith
  · simp

end PiExponent.WeightedCurveDegree

end OAI
