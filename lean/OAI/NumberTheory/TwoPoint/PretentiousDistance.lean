import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

namespace OAI

/-!
# The pretentious distance used in ordinary two-point correlations

These definitions use the prime cutoff and the twist-height cutoff at the same
integer scale.  The finite-prime perturbation estimate below is Lemma
`lem:finite-prime-stability` of *Ordinary two-point correlations of
multiplicative functions* (24 September 2026).  It is elementary and does not
assume any analytic input.
-/

namespace TwoPointCorrelations

open scoped ComplexConjugate
open Filter Finset

/-- The primes not exceeding an integer cutoff. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- The square of the pretentious distance; the second sequence can be any twist. -/
noncomputable def squaredDistance (f g : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, (1 - (f p * conj (g p)).re) / (p : ℝ)

/-- The sequence `χ(n) n^(it)`, with the value at zero immaterial to the prime sum. -/
noncomputable def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Uniform nonpretentiousness against every fixed Dirichlet character.

The quantifier over all real lower bounds expresses divergence of the squared
distance uniformly over `|t| ≤ N`.  As the distance is nonnegative, this is
exactly the divergence of the distance appearing in the manuscript.
-/
def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q) (K : ℝ),
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, |t| ≤ (N : ℝ) →
      K ≤ squaredDistance f (characterTwist χ t) N

lemma characterTwist_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ‖characterTwist χ t n‖ ≤ 1 := by
  simpa only [characterTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
    χ.norm_le_one (n : ZMod q)

lemma squaredDistance_nonneg (f g : ℕ → ℂ) (N : ℕ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    0 ≤ squaredDistance f g N := by
  apply Finset.sum_nonneg
  intro p hp
  apply div_nonneg
  · have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
      calc
        ‖f p * conj (g p)‖ = ‖f p‖ * ‖g p‖ := by simp
        _ ≤ 1 * 1 := mul_le_mul (hf p) (hg p) (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hnorm)
  · positivity

lemma squaredDistance_conj (f g : ℕ → ℂ) (N : ℕ) :
    squaredDistance (fun n => conj (f n)) (fun n => conj (g n)) N =
      squaredDistance f g N := by
  unfold squaredDistance
  apply Finset.sum_congr rfl
  intro p hp
  congr 2
  rw [← map_mul]
  simp

/-- Conjugating a character and reversing the height conjugates its twist. -/
lemma characterTwist_conj {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) :
    characterTwist (χ.ringHomComp (starRingEnd ℂ)) (-t) n =
      conj (characterTwist χ t n) := by
  simp only [characterTwist, MulChar.ringHomComp_apply, map_mul,
    ← Complex.exp_conj]
  congr 2
  simp only [neg_mul, Complex.ofReal_neg, Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-- Uniform nonpretentiousness is invariant under complex conjugation. -/
lemma UniformlyNonpretentious.conj {f : ℕ → ℂ}
    (hf : UniformlyNonpretentious f) :
    UniformlyNonpretentious (fun n => conj (f n)) := by
  intro q hq χ K
  filter_upwards [hf q hq (χ.ringHomComp (starRingEnd ℂ)) K] with N hN
  intro t ht
  have h := hN (-t) (by simpa using ht)
  have heq : characterTwist (χ.ringHomComp (starRingEnd ℂ)) (-t) =
      fun n => conj (characterTwist χ t n) := by
    funext n
    exact characterTwist_conj χ t n
  rw [heq] at h
  simpa only [← squaredDistance_conj f (fun n => conj (characterTwist χ t n)) N,
    Complex.conj_conj] using h

/-- Altering a fixed finite set of prime values changes the square of the
pretentious distance by at most twice their reciprocal sum. -/
lemma squaredDistance_finite_prime_change (f b g : ℕ → ℂ) (N : ℕ)
    (P : Finset ℕ) (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hb : ∀ n, 0 < n → ‖b n‖ ≤ 1)
    (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    (heq : ∀ p, Nat.Prime p → p ∉ P → b p = f p) :
    |squaredDistance b g N - squaredDistance f g N| ≤
      2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  let S := primesUpTo N
  have hterm (p : ℕ) (hp : 0 < p) :
      |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| ≤ 2 / (p : ℝ) := by
    have hdiff : ‖f p - b p‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith [hf p hp, hb p hp])
    have hprod : ‖(f p - b p) * conj (g p)‖ ≤ 2 := by
      calc
        ‖(f p - b p) * conj (g p)‖ = ‖f p - b p‖ * ‖g p‖ := by simp
        _ ≤ 2 * 1 := mul_le_mul hdiff (hg p hp) (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hre : |(f p * conj (g p)).re - (b p * conj (g p)).re| ≤ 2 := by
      calc
        |(f p * conj (g p)).re - (b p * conj (g p)).re| =
          |((f p - b p) * conj (g p)).re| := by rw [sub_mul, Complex.sub_re]
        _ ≤ ‖(f p - b p) * conj (g p)‖ := Complex.abs_re_le_norm _
        _ ≤ 2 := hprod
    rw [← sub_div, show (1 - (b p * conj (g p)).re) -
      (1 - (f p * conj (g p)).re) =
        (f p * conj (g p)).re - (b p * conj (g p)).re by ring,
      abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
    exact div_le_div_of_nonneg_right hre (Nat.cast_nonneg p)
  have htermP (p : ℕ) (hp : p ∈ S) :
      |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| ≤
      if p ∈ P then 2 / (p : ℝ) else 0 := by
    split_ifs with hP
    · exact hterm p ((Finset.mem_filter.mp hp).2.pos)
    · have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      rw [heq p hprime hP, sub_self, abs_zero]
  calc
    |squaredDistance b g N - squaredDistance f g N| =
      |∑ p ∈ S, ((1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ))| := by
          rw [Finset.sum_sub_distrib]
          rfl
    _ ≤ ∑ p ∈ S, |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, if p ∈ P then 2 / (p : ℝ) else 0 := Finset.sum_le_sum htermP
    _ = ∑ p ∈ S.filter (fun p => p ∈ P), 2 / (p : ℝ) := by rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp hnot
        positivity
    _ = 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The bound is uniform over the changing twist and finite modifications. -/
lemma UniformlyNonpretentious.finite_prime_change {f b : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (P : Finset ℕ)
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hb : ∀ n, 0 < n → ‖b n‖ ≤ 1)
    (heq : ∀ p, Nat.Prime p → p ∉ P → b p = f p) :
    UniformlyNonpretentious b := by
  intro q hq χ K
  filter_upwards [hfnp q hq χ (K + 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ))] with N hN
  intro t ht
  have hdist := squaredDistance_finite_prime_change f b (characterTwist χ t) N
    P hf hb (fun n _ => characterTwist_norm_le_one χ t n) heq
  have hlow := hN t ht
  have := (abs_le.mp hdist).1
  linarith

/-- One lower bound works for every member of a fixed finite character family,
and for every bounded sequence whose prime values are changed only in `P`.
This is the uniformity needed when taking the short-interval theorem at a fixed
auxiliary graph scale. -/
lemma UniformlyNonpretentious.finite_family {ι : Type*} [Finite ι]
    {f : ℕ → ℂ} (hfnp : UniformlyNonpretentious f) (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : Finset ℕ) (q : ι → ℕ) (hq : ∀ i, 0 < q i)
    (χ : ∀ i, DirichletCharacter ℂ (q i)) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ i (b : ℕ → ℂ),
      (∀ n, 0 < n → ‖b n‖ ≤ 1) →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ t : ℝ, |t| ≤ (N : ℝ) → K ≤ squaredDistance b (characterTwist (χ i) t) N := by
  have hfamily : ∀ᶠ N : ℕ in atTop, ∀ i,
      ∀ t : ℝ, |t| ≤ (N : ℝ) →
        K + 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤
          squaredDistance f (characterTwist (χ i) t) N := by
    rw [Filter.eventually_all]
    intro i
    exact hfnp (q i) (hq i) (χ i) _
  filter_upwards [hfamily] with N hN
  intro i b hb heq t ht
  have hdist := squaredDistance_finite_prime_change f b (characterTwist (χ i) t) N
    P hf hb (fun n _ => characterTwist_norm_le_one (χ i) t n) heq
  have hlow := hN i t ht
  have := (abs_le.mp hdist).1
  linarith

end TwoPointCorrelations

end OAI
