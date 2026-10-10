import OAI.Probability.InvariantIsing.Core.Model

namespace OAI

/-! Finite entropy and the log-sum variational bound used to project
canonical spins onto an attainable constrained block. Zero trial masses
are allowed and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def finiteShannonEntropy {X : Type*} [Fintype X] (p : X → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

lemma finite_relativeEntropy_nonneg_of_sum_le {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hqSum : ∑ x, q x ≤ 1) :
    0 ≤ ∑ x, p x * Real.log (p x / q x) := by
  have hi (x : X) : p x - q x ≤ p x * Real.log (p x / q x) := by
    by_cases hx : p x = 0
    · simp only [hx, zero_sub, zero_mul]
      exact neg_nonpos.mpr (hq x).le
    have hxp : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
    have hl := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hq x) hxp)) (hp x)
    have he : p x * (q x / p x - 1) = q x - p x := by field_simp
    rw [he, Real.log_div (hq x).ne' hx] at hl
    rw [Real.log_div hx (hq x).ne']
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hi x)
  rw [Finset.sum_sub_distrib, hpSum] at hs
  linarith

lemma finite_relativeEntropy_nonneg {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hqSum : ∑ x, q x = 1) :
    0 ≤ ∑ x, p x * Real.log (p x / q x) :=
  finite_relativeEntropy_nonneg_of_sum_le p q hp hpSum hq hqSum.le

def finiteCanonicalWeights {X : Type*} [Fintype X] (H : X → ℝ) (x : X) : ℝ :=
  Real.exp (H x) / ∑ y, Real.exp (H y)

lemma finiteCanonicalWeights_pos {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (x : X) : 0 < finiteCanonicalWeights H x :=
  div_pos (Real.exp_pos _) (sum_exp_pos H)

lemma finiteCanonicalWeights_sum {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) : ∑ x, finiteCanonicalWeights H x = 1 := by
  simp only [finiteCanonicalWeights, ← Finset.sum_div]
  exact div_self (sum_exp_pos H).ne'

lemma log_sum_exp_ge_trial {X : Type*} [Fintype X] [Nonempty X]
    (H p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1) :
    (∑ x, p x * H x) + finiteShannonEntropy p ≤ Real.log (∑ x, Real.exp (H x)) := by
  have hk := finite_relativeEntropy_nonneg p (finiteCanonicalWeights H) hp hpSum
    (finiteCanonicalWeights_pos H) (finiteCanonicalWeights_sum H)
  have hi (x : X) : p x * Real.log (p x / finiteCanonicalWeights H x) =
      p x * Real.log (p x) - p x * H x + p x * Real.log (∑ y, Real.exp (H y)) := by
    by_cases hx : p x = 0
    · simp [hx]
    · rw [Real.log_div hx (finiteCanonicalWeights_pos H x).ne', finiteCanonicalWeights,
        Real.log_div (Real.exp_ne_zero _) (sum_exp_pos H).ne', Real.log_exp]
      ring
  simp_rw [hi] at hk
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hpSum, one_mul] at hk
  unfold finiteShannonEntropy
  linarith

lemma log_sum_exp_eq_canonical {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    Real.log (∑ x, Real.exp (H x)) =
      (∑ x, finiteCanonicalWeights H x * H x) + finiteShannonEntropy (finiteCanonicalWeights H) := by
  have he (x : X) : finiteCanonicalWeights H x * Real.log (finiteCanonicalWeights H x) =
      finiteCanonicalWeights H x * H x -
        finiteCanonicalWeights H x * Real.log (∑ y, Real.exp (H y)) := by
    conv_lhs => arg 2; rw [finiteCanonicalWeights, Real.log_div (Real.exp_ne_zero _)
      (sum_exp_pos H).ne', Real.log_exp]
    ring
  unfold finiteShannonEntropy
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, finiteCanonicalWeights_sum, one_mul]
  ring

end InvariantIsing

end

end OAI
