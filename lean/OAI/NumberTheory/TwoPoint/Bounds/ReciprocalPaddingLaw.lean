import OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
import OAI.NumberTheory.TwoPoint.Bounds.BernoulliTail

namespace OAI

/-! The harmonic divisor law `4^omega(q)/(q S)` is an actual finite
independent prime-selection law with inclusion probabilities `4/(p+4)`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def reciprocalPaddingPrimeLaw (p : ℕ) : FiniteLaw Bool :=
  booleanLaw (4 / ((p : ℝ) + 4)) (by positivity) (by
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg p))

noncomputable def reciprocalPaddingLaw (Q : Finset ℕ) : FiniteLaw (Q → Bool) :=
  FiniteLaw.independent (fun p : Q => reciprocalPaddingPrimeLaw p)

lemma reciprocal_padding_atom (p : ℕ) (hp : 0 < p) (b : Bool) :
    (reciprocalPaddingPrimeLaw p).weight b * (1 + 4 / (p : ℝ)) =
      if b then 4 / (p : ℝ) else 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hp4 : (p : ℝ) + 4 ≠ 0 := by positivity
  cases b <;> simp only [reciprocalPaddingPrimeLaw, booleanLaw, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp <;> ring

lemma paddingSelectedDivisor_cast (Q : Finset ℕ) (b : Q → Bool) :
    (paddingSelectedDivisor Q b : ℝ) = ∏ p : Q, if b p then (p.val : ℝ) else 1 := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  simp only [selectedCoordinates, prod_filter]

lemma reciprocal_padding_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (b : Q → Bool) :
    (reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q =
      paddingDivisorCoefficient Q b / (paddingSelectedDivisor Q b : ℝ) := by
  simp only [reciprocalPaddingLaw, FiniteLaw.independent, paddingTiltNormalizer,
    ← prod_mul_distrib]
  rw [paddingDivisorCoefficient, paddingSelectedDivisor_cast, ← prod_div_distrib]
  apply prod_congr rfl
  intro p _
  rw [reciprocal_padding_atom p (hQ p p.property).pos]
  cases b p <;> simp

lemma reciprocal_padding_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (F : ℕ → ℝ) :
    (reciprocalPaddingLaw Q).average (fun b => F (paddingSelectedDivisor Q b)) =
      (paddingTiltNormalizer Q)⁻¹ *
        ∑ q ∈ retainedPrimeDivisors Q, ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q := by
  have hS := paddingTiltNormalizer_pos Q
  let G (q : retainedPrimeDivisors Q) : ℝ :=
    ((4 : ℝ) ^ q.val.primeFactors.card / (q.val : ℝ)) * F q.val
  have hatom (b : Q → Bool) :
      (reciprocalPaddingLaw Q).weight b * F (paddingSelectedDivisor Q b) =
        (paddingTiltNormalizer Q)⁻¹ * G (paddingDivisorEquiv Q hQ b) := by
    have hw := reciprocal_padding_weight Q hQ b
    change _ = (paddingTiltNormalizer Q)⁻¹ *
      ((4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card /
        (paddingSelectedDivisor Q b : ℝ) * F (paddingSelectedDivisor Q b))
    rw [paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
      ← paddingDivisorCoefficient_eq_four_pow]
    calc
      _ = (paddingTiltNormalizer Q)⁻¹ *
          (((reciprocalPaddingLaw Q).weight b * paddingTiltNormalizer Q) *
            F (paddingSelectedDivisor Q b)) := by field_simp [hS.ne']
      _ = _ := by rw [hw]
  unfold FiniteLaw.average
  simp_rw [hatom]
  rw [← mul_sum, (paddingDivisorEquiv Q hQ).sum_comp G]
  congr 1
  exact sum_coe_sort (retainedPrimeDivisors Q)
    (fun q : ℕ => ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) * F q)

lemma FiniteLaw.independent_average_coordinate {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] (μ : ι → FiniteLaw A) (i : ι) (f : A → ℝ) :
    (FiniteLaw.independent μ).average (fun x => f (x i)) = (μ i).average f := by
  have hh := FiniteLaw.independent_average_product μ (fun j x => if j = i then f x else 1)
  have he (j : ι) : (μ j).average (fun x => if j = i then f x else 1) =
      if j = i then (μ i).average f else 1 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  simpa only [he, prod_ite_eq', mem_univ, ite_true] using hh

lemma reciprocal_padding_count_average (Q : Finset ℕ) :
    (reciprocalPaddingLaw Q).average booleanCount = ∑ p : Q, 4 / ((p.val : ℝ) + 4) := by
  change (FiniteLaw.independent (fun p : Q => reciprocalPaddingPrimeLaw p)).average
    (fun b : Q → Bool => ∑ p : Q, if b p then 1 else 0) = _
  rw [FiniteLaw.average_sum]
  apply sum_congr rfl
  intro p _
  rw [FiniteLaw.independent_average_coordinate (fun p : Q => reciprocalPaddingPrimeLaw p) p
    (fun b : Bool => if b then 1 else 0)]
  simp [reciprocalPaddingPrimeLaw, booleanLaw, FiniteLaw.average]

lemma reciprocal_padding_log_average (Q : Finset ℕ) :
    (reciprocalPaddingLaw Q).average (paddingLog Q) =
      ∑ p : Q, (4 / ((p.val : ℝ) + 4)) * Real.log p.val := by
  change (FiniteLaw.independent (fun p : Q => reciprocalPaddingPrimeLaw p)).average
    (fun b : Q → Bool => ∑ p : Q, if b p then Real.log p.val else 0) = _
  rw [FiniteLaw.average_sum]
  apply sum_congr rfl
  intro p _
  rw [FiniteLaw.independent_average_coordinate (fun p : Q => reciprocalPaddingPrimeLaw p) p
    (fun b : Bool => if b then Real.log p.val else 0)]
  simp [reciprocalPaddingPrimeLaw, booleanLaw, FiniteLaw.average]

end TwoPointCorrelations

end OAI
