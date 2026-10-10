import OAI.Analysis.KadisonKastler.TracialCauchySchwarz
import OAI.Analysis.KadisonKastler.FinitePhases
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Logic.Equiv.Basic

namespace OAI

/-! # Fourth moments of finite independent signs

The finite probability space is the set of all Boolean sign assignments.
The four-sign identity and tracial Cauchy–Schwarz give the estimate used
in the bounded-vector test in manuscript §5.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate signs on the uniform finite Boolean probability space. -/
def finiteSign (ε : ι → Bool) (i : ι) : ℝ := if ε i then -1 else 1

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem finiteSign_sq (ε : ι → Bool) (i : ι) : finiteSign ε i ^ 2 = 1 := by
  cases h : ε i <;> simp [finiteSign, h]

private def flipSign (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun ε := Function.update ε i (!(ε i))
  invFun ε := Function.update ε i (!(ε i))
  left_inv ε := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]
  right_inv ε := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]

omit [Fintype ι] in
private theorem finiteSign_flip_same (ε : ι → Bool) (i : ι) :
    finiteSign (flipSign i ε) i = -finiteSign ε i := by
  cases h : ε i <;> simp [finiteSign, flipSign, h]

omit [Fintype ι] in
private theorem finiteSign_flip_ne (ε : ι → Bool) {i j : ι} (h : j ≠ i) :
    finiteSign (flipSign i ε) j = finiteSign ε j := by
  simp [finiteSign, flipSign, Function.update_of_ne h]

/-- Coordinate sign orthogonality. -/
theorem finiteSign_pair (i j : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true, ← pow_two, finiteSign_sq, Fintype.expect_const]
  · rw [ite_eq_right h]
    have he := Fintype.expect_equiv (flipSign i)
      (fun ε => finiteSign ε i * finiteSign ε j)
      (fun ε => -(finiteSign ε i * finiteSign ε j)) (by
        intro ε
        rw [finiteSign_flip_same, finiteSign_flip_ne ε (Ne.symm h)]
        ring)
    rw [Finset.expect_neg_distrib] at he
    linarith

/-- A sign appearing exactly once kills a four-sign expectation. -/
private theorem finiteSign_four_single (i j k l : ι)
    (hij : j ≠ i) (hik : k ≠ i) (hil : l ≠ i) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j *
      finiteSign ε k * finiteSign ε l) = 0 := by
  have he := Fintype.expect_equiv (flipSign i)
    (fun ε => finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l)
    (fun ε => -(finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l)) (by
      intro ε
      rw [finiteSign_flip_same, finiteSign_flip_ne ε hij,
        finiteSign_flip_ne ε hik, finiteSign_flip_ne ε hil]
      ring)
  rw [Finset.expect_neg_distrib] at he
  linarith

/-- The three pairings, with the common diagonal counted only once. -/
theorem finiteSign_four (i j k l : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j *
      finiteSign ε k * finiteSign ε l) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) -
      (if i = j ∧ j = k ∧ k = l then 2 else 0) := by
  by_cases hij : i = j
  · subst j
    have he (ε : ι → Bool) :
        finiteSign ε i * finiteSign ε i * finiteSign ε k * finiteSign ε l =
          finiteSign ε k * finiteSign ε l := by
      rw [← pow_two, finiteSign_sq, one_mul]
    simp_rw [he]
    rw [finiteSign_pair]
    by_cases hik : i = k <;> by_cases hkl : k = l <;>
      simp_all
    all_goals norm_num
  · by_cases hik : i = k
    · subst k
      have he (ε : ι → Bool) :
          finiteSign ε i * finiteSign ε j * finiteSign ε i * finiteSign ε l =
            finiteSign ε j * finiteSign ε l := by
        calc
          _ = finiteSign ε i ^ 2 * (finiteSign ε j * finiteSign ε l) := by ring
          _ = _ := by rw [finiteSign_sq, one_mul]
      simp_rw [he]
      rw [finiteSign_pair]
      simp [hij, Ne.symm hij]
    · by_cases hil : i = l
      · subst l
        have he (ε : ι → Bool) :
            finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε i =
              finiteSign ε j * finiteSign ε k := by
          calc
            _ = finiteSign ε i ^ 2 * (finiteSign ε j * finiteSign ε k) := by ring
            _ = _ := by rw [finiteSign_sq, one_mul]
        simp_rw [he]
        rw [finiteSign_pair]
        simp [hij, hik, Ne.symm hij]
      · rw [finiteSign_four_single i j k l (Ne.symm hij) (Ne.symm hik) (Ne.symm hil)]
        simp [hij, hik, hil]

/-- The fourth-sign identity integrated against any four-index coefficient. -/
theorem expect_finiteSign_four_sum (F : ι → ι → ι → ι → ℝ) :
    (𝔼 ε : ι → Bool, ∑ i, ∑ j, ∑ k, ∑ l,
      (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) * F i j k l) =
      (∑ i, ∑ k, F i i k k) + (∑ i, ∑ j, F i j i j) +
        (∑ i, ∑ j, F i j j i) - 2 * ∑ i, F i i i i := by
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_four,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [ite_and, Finset.mul_sum]

variable {B : Type*} [CStarAlgebra B]

/-- The real part of the trace, viewed as a real-linear functional. -/
def realTrace (τ : FaithfulTracialState B) : B →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (τ.toLinearMap.restrictScalars ℝ)

@[simp]
theorem realTrace_apply (τ : FaithfulTracialState B) (x : B) :
    realTrace τ x = (τ.toLinearMap x).re := rfl

/-- The unnormalized random sum; normalization is introduced after expansion. -/
def finiteSignSum (a : ι → B) (ε : ι → Bool) : B := ∑ i, finiteSign ε i • a i

omit [DecidableEq ι] in
private theorem fourth_integrand_expand (τ : FaithfulTracialState B)
    (a : ι → B) (ε : ι → Bool) :
    realTrace τ ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (finiteSign ε i * finiteSign ε j * finiteSign ε k * finiteSign ε l) *
          realTrace τ ((star (a i) * a j) * (star (a k) * a l)) := by
  have hprod : star (finiteSignSum a ε) * finiteSignSum a ε =
      ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) • (star (a i) * a j) := by
    simp only [finiteSignSum, star_sum, star_smul, star_trivial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_comm (finiteSign ε j) (finiteSign ε i)]
  rw [hprod, pow_two, Finset.sum_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [DecidableEq ι] in
private theorem realTrace_sum_square (τ : FaithfulTracialState B) (f : ι → B) :
    realTrace τ ((∑ i, f i) ^ 2) = ∑ i, ∑ j, realTrace τ (f i * f j) := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]

/-- Exact fourth-moment pairing formula before scalar normalization. -/
theorem expect_finiteSignSum_fourth (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool, realTrace τ ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) =
      realTrace τ ((∑ i, star (a i) * a i) ^ 2) +
        (∑ i, ∑ j, realTrace τ ((star (a i) * a j) ^ 2)) +
        realTrace τ ((∑ i, a i * star (a i)) ^ 2) -
        2 * ∑ i, realTrace τ ((star (a i) * a i) ^ 2) := by
  simp_rw [fourth_integrand_expand]
  rw [expect_finiteSign_four_sum]
  have hcross (i j : ι) :
      realTrace τ ((star (a i) * a j) * (star (a j) * a i)) =
        realTrace τ ((a i * star (a i)) * (a j * star (a j))) := by
    simp only [realTrace_apply]
    have ht : τ.toLinearMap ((star (a i) * a j) * (star (a j) * a i)) =
        τ.toLinearMap ((a i * star (a i)) * (a j * star (a j))) := by
      calc
        _ = τ.toLinearMap ((a j * (star (a j) * a i)) * star (a i)) := by
          rw [mul_assoc, τ.tracial (star (a i))]
        _ = τ.toLinearMap ((a j * star (a j)) * (a i * star (a i))) := by
          simp only [mul_assoc]
        _ = _ := τ.tracial _ _
    exact congrArg Complex.re ht
  have hsum : (∑ i, ∑ j, realTrace τ ((star (a i) * a j) * (star (a j) * a i))) =
      realTrace τ ((∑ i, a i * star (a i)) ^ 2) := by
    rw [realTrace_sum_square]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hcross i j
  rw [hsum, realTrace_sum_square τ (fun i => star (a i) * a i)]
  simp only [pow_two]

/-- Tracial Cauchy–Schwarz bounds the crossed pairing by a covariance term. -/
theorem realTrace_square_le_star_square (τ : FaithfulTracialState B) (x : B) :
    realTrace τ (x ^ 2) ≤ realTrace τ (star x * x) := by
  calc
    _ ≤ ‖τ.toLinearMap (x ^ 2)‖ := Complex.re_le_norm _
    _ ≤ traceTwoNorm τ x ^ 2 := by
      simpa only [star_star, traceTwoNorm_star, pow_two] using τ.cauchySchwarz (star x) x
    _ = _ := traceTwoNorm_sq τ x

/-- The unnormalized fourth moment is controlled by the two covariance squares. -/
theorem expect_finiteSignSum_fourth_le (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool, realTrace τ ((star (finiteSignSum a ε) * finiteSignSum a ε) ^ 2)) ≤
      realTrace τ ((∑ i, star (a i) * a i) ^ 2) +
        2 * realTrace τ ((∑ i, a i * star (a i)) ^ 2) := by
  rw [expect_finiteSignSum_fourth]
  have hcross : (∑ i, ∑ j, realTrace τ ((star (a i) * a j) ^ 2)) ≤
      realTrace τ ((∑ i, a i * star (a i)) ^ 2) := by
    calc
      _ ≤ ∑ i, ∑ j, realTrace τ (star (star (a i) * a j) * (star (a i) * a j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          realTrace_square_le_star_square τ _
      _ = _ := by
        rw [realTrace_sum_square]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [realTrace_apply, star_mul, star_star]
        have ht := τ.tracial (star (a j)) (a i * (star (a i) * a j))
        simpa only [mul_assoc] using congrArg Complex.re ht
  have hdiag : 0 ≤ ∑ i, realTrace τ ((star (a i) * a i) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    simpa only [realTrace_apply, pow_two, star_mul, star_star] using
      τ.positive (star (a i) * a i)
  linarith

/-- The usual variance-one normalization of the finite sign sum. -/
def normalizedFiniteSignSum (a : ι → B) (ε : ι → Bool) : B :=
  (Real.sqrt (Fintype.card ι : ℝ))⁻¹ • finiteSignSum a ε

/-- Right covariance of the coefficients. -/
def finiteSignRightCovariance (a : ι → B) : B :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, star (a i) * a i

/-- Left covariance of the coefficients. -/
def finiteSignLeftCovariance (a : ι → B) : B :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, a i * star (a i)

private theorem realTrace_square_smul (τ : FaithfulTracialState B) (t : ℝ) (x : B) :
    realTrace τ ((t • x) ^ 2) = t ^ 2 * realTrace τ (x ^ 2) := by
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, map_smul, smul_eq_mul]

private theorem realTrace_fourth_smul (τ : FaithfulTracialState B) (t : ℝ) (x : B) :
    realTrace τ ((star (t • x) * (t • x)) ^ 2) =
      t ^ 4 * realTrace τ ((star x * x) ^ 2) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, realTrace_square_smul]
  ring

/-- The normalized fourth moment is bounded by the two covariance squares. -/
theorem expect_normalizedFiniteSignSum_fourth_le
    (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool,
      realTrace τ ((star (normalizedFiniteSignSum a ε) * normalizedFiniteSignSum a ε) ^ 2)) ≤
      traceTwoNorm τ (finiteSignRightCovariance a) ^ 2 +
        2 * traceTwoNorm τ (finiteSignLeftCovariance a) ^ 2 := by
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 4 = (Fintype.card ι : ℝ)⁻¹ ^ 2 := by
    rw [inv_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _), inv_pow]
  have hright : star (finiteSignRightCovariance a) = finiteSignRightCovariance a := by
    simp [finiteSignRightCovariance, star_sum, star_smul, star_mul]
  have hleft : star (finiteSignLeftCovariance a) = finiteSignLeftCovariance a := by
    simp [finiteSignLeftCovariance, star_sum, star_smul, star_mul]
  have hright2 : traceTwoNorm τ (finiteSignRightCovariance a) ^ 2 =
      realTrace τ (finiteSignRightCovariance a ^ 2) := by
    simpa only [hright, pow_two, realTrace_apply] using
      traceTwoNorm_sq τ (finiteSignRightCovariance a)
  have hleft2 : traceTwoNorm τ (finiteSignLeftCovariance a) ^ 2 =
      realTrace τ (finiteSignLeftCovariance a ^ 2) := by
    simpa only [hleft, pow_two, realTrace_apply] using
      traceTwoNorm_sq τ (finiteSignLeftCovariance a)
  simp_rw [normalizedFiniteSignSum, realTrace_fourth_smul]
  rw [← Finset.mul_expect, hs, hright2, hleft2,
    finiteSignRightCovariance, finiteSignLeftCovariance,
    realTrace_square_smul, realTrace_square_smul]
  have h := mul_le_mul_of_nonneg_left (expect_finiteSignSum_fourth_le τ a)
    (sq_nonneg ((Fintype.card ι : ℝ)⁻¹))
  nlinarith only [h]

/-- Covariance two-norms bounded by two give the manuscript constant twelve. -/
theorem expect_normalizedFiniteSignSum_fourth_le_twelve
    (τ : FaithfulTracialState B) (a : ι → B)
    (hQ : traceTwoNorm τ (finiteSignRightCovariance a) ≤ 2)
    (hL : traceTwoNorm τ (finiteSignLeftCovariance a) ≤ 2) :
    (𝔼 ε : ι → Bool,
      (τ.toLinearMap ((star (normalizedFiniteSignSum a ε) *
        normalizedFiniteSignSum a ε) ^ 2)).re) ≤ 12 := by
  have h := expect_normalizedFiniteSignSum_fourth_le τ a
  have hQ0 := traceTwoNorm_nonneg τ (finiteSignRightCovariance a)
  have hL0 := traceTwoNorm_nonneg τ (finiteSignLeftCovariance a)
  change (𝔼 ε : ι → Bool,
    realTrace τ ((star (normalizedFiniteSignSum a ε) * normalizedFiniteSignSum a ε) ^ 2)) ≤ 12
  nlinarith

/-- Real signs also form an orthogonal family of complex phases. -/
theorem finiteSign_complex_pair (i j : ι) :
    (𝔼 ε : ι → Bool, star (finiteSign ε i : ℂ) * (finiteSign ε j : ℂ)) =
      if i = j then 1 else 0 := by
  let toC : ℝ →ₗ[ℚ≥0] ℂ := Complex.ofRealCLM.toLinearMap.restrictScalars ℚ≥0
  have h := congrArg toC (finiteSign_pair i j)
  rw [map_expect] at h
  simpa [toC, Complex.ofReal_mul] using h

private theorem expect_finiteSign_pair_sum (F : ι → ι → ℝ) :
    (𝔼 ε : ι → Bool, ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) * F i j) =
      ∑ i, F i i := by
  simp only [Finset.expect_sum_comm, ← Finset.expect_mul, finiteSign_pair]
  simp

/-- The second moment is the average of the coefficient two-norm squares. -/
theorem expect_normalizedFiniteSignSum_twoNorm_sq
    (τ : FaithfulTracialState B) (a : ι → B) :
    (𝔼 ε : ι → Bool, traceTwoNorm τ (normalizedFiniteSignSum a ε) ^ 2) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, traceTwoNorm τ (a i) ^ 2 := by
  have hprod (ε : ι → Bool) :
      realTrace τ (star (finiteSignSum a ε) * finiteSignSum a ε) =
        ∑ i, ∑ j, (finiteSign ε i * finiteSign ε j) * realTrace τ (star (a i) * a j) := by
    simp only [finiteSignSum, star_sum, star_smul, star_trivial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, map_sum, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_comm (finiteSign ε j) (finiteSign ε i)]
  have hs : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [traceTwoNorm_sq, normalizedFiniteSignSum, star_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  change (𝔼 ε : ι → Bool, realTrace τ
    (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * (Real.sqrt (Fintype.card ι : ℝ))⁻¹) •
      (star (finiteSignSum a ε) * finiteSignSum a ε))) = _
  simp_rw [map_smul, smul_eq_mul, ← pow_two, hs, hprod]
  rw [← Finset.mul_expect, expect_finiteSign_pair_sum]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq ι] in
private theorem map_normalizedFiniteSignSum (J : B →ₗ[ℂ] H) (a : ι → B) (ε : ι → Bool) :
    J (normalizedFiniteSignSum a ε) =
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) •
        finitePhaseSum (fun i ε => (finiteSign ε i : ℂ)) (fun i => J (a i)) ε := by
  simp only [normalizedFiniteSignSum, finiteSignSum, finitePhaseSum,
    ← Complex.coe_smul, map_smul, map_sum, Complex.ofReal_inv]

/-- Mixed sign orthogonality, with any complex-linear realization and bounded operator. -/
theorem expect_normalizedFiniteSignSum_pairing
    (J : B →ₗ[ℂ] H) (V : H →L[ℂ] H) (a b : ι → B) :
    (𝔼 ε : ι → Bool, inner ℂ (V (J (normalizedFiniteSignSum a ε)))
      (J (normalizedFiniteSignSum b ε))) =
      (Fintype.card ι : ℂ)⁻¹ * ∑ i, inner ℂ (V (J (a i))) (J (b i)) := by
  let χ (i : ι) (ε : ι → Bool) : ℂ := finiteSign ε i
  have hmap (ε : ι → Bool) :
      V (finitePhaseSum χ (fun i => J (a i)) ε) =
        finitePhaseSum χ (fun i => V (J (a i))) ε := by
    simp only [finitePhaseSum, map_sum, map_smul]
  have hc : star (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) = (Fintype.card ι : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← pow_two, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast]
  simp_rw [map_normalizedFiniteSignSum, map_smul]
  change (𝔼 ε : ι → Bool, inner ℂ
    ((((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) •
      V (finitePhaseSum χ (fun i => J (a i)) ε))
    ((((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) •
      finitePhaseSum χ (fun i => J (b i)) ε)) = _
  simp_rw [hmap, inner_smul_left, inner_smul_right, starRingEnd_apply, ← mul_assoc, hc]
  rw [← Finset.mul_expect]
  congr 1
  exact finitePhaseSum_inner χ finiteSign_complex_pair _ _

end

end KadisonKastler

end OAI
