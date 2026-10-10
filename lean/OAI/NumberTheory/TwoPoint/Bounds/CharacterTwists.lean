import OAI.NumberTheory.TwoPoint.Basic
import OAI.NumberTheory.TwoPoint.PretentiousDistance

namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped ComplexConjugate
open Filter

/-- Product of two characters, viewed at their common product modulus. -/
noncomputable def productCharacters {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q * r) :=
  χ.changeLevel (Nat.dvd_mul_right q r) * ψ.changeLevel (Nat.dvd_mul_left r q)

/-- Conjugation of the values of a Dirichlet character. -/
def conjugateCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : DirichletCharacter ℂ q :=
  χ.ringHomComp (starRingEnd ℂ)

@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl

/-- Changing both character levels to their product preserves their pointwise
product, even when the argument is not a unit modulo the product. -/
lemma productCharacters_apply_nat {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    productCharacters χ ψ (n : ZMod (q * r)) = χ (n : ZMod q) * ψ (n : ZMod r) := by
  unfold productCharacters
  simp only [MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hcop : n.Coprime (q * r)
  · have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
      (Nat.dvd_mul_right q r) hcop.isCoprime
    have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ
      (Nat.dvd_mul_left r q) hcop.isCoprime
    simpa only [Int.cast_natCast] using congrArg₂ (· * ·) hχ hψ
  · have hunit : ¬IsUnit (n : ZMod (q * r)) := by
      simpa only [ZMod.isUnit_iff_coprime] using hcop
    rw [MulChar.map_nonunit _ hunit, zero_mul]
    by_cases hnq : n.Coprime q
    · have hnr : ¬n.Coprime r := by
        intro hnr
        exact hcop (hnq.mul_right hnr)
      have hunitr : ¬IsUnit (n : ZMod r) := by
        simpa only [ZMod.isUnit_iff_coprime] using hnr
      rw [MulChar.map_nonunit ψ hunitr, mul_zero]
    · have hunitq : ¬IsUnit (n : ZMod q) := by
        simpa only [ZMod.isUnit_iff_coprime] using hnq
      rw [MulChar.map_nonunit χ hunitq, zero_mul]

/-- Multiplication by a fixed Dirichlet character. -/
noncomputable def twistByCharacter {q : ℕ} (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := f n * χ (n : ZMod q)

lemma characterTwist_productCharacters {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (t : ℝ) (n : ℕ) :
    characterTwist (productCharacters χ ψ) t n =
      characterTwist χ t n * ψ (n : ZMod r) := by
  unfold characterTwist
  rw [productCharacters_apply_nat]
  ring

/-- The same real twist height appears on both sides, including at primes
dividing either character modulus. -/
lemma squaredDistance_twistByCharacter {q r : ℕ} (f : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ r) (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    squaredDistance (TwoPointCorrelations.twistByCharacter f ψ) (characterTwist χ t) N =
      squaredDistance f (characterTwist (productCharacters χ (conjugateCharacter ψ)) t) N := by
  unfold squaredDistance
  apply Finset.sum_congr rfl
  intro p hp
  rw [characterTwist_productCharacters]
  simp only [TwoPointCorrelations.twistByCharacter, map_mul, conjugateCharacter_apply, Complex.conj_conj]
  congr 2
  congr 1
  ring

lemma UniformlyNonpretentious.twistByCharacter {r : ℕ} {f : ℕ → ℂ}
    (hf : UniformlyNonpretentious f) (ψ : DirichletCharacter ℂ r) (hr : 0 < r) :
    UniformlyNonpretentious (TwoPointCorrelations.twistByCharacter f ψ) := by
  intro q hq χ K
  filter_upwards [hf (q * r) (Nat.mul_pos hq hr)
    (productCharacters χ (conjugateCharacter ψ)) K] with N hN
  intro t ht
  rw [squaredDistance_twistByCharacter]
  exact hN t ht

lemma OneBounded.twistByCharacter {q : ℕ} {f : ℕ → ℂ}
    (hf : OneBounded f) (χ : DirichletCharacter ℂ q) : OneBounded (TwoPointCorrelations.twistByCharacter f χ) := by
  intro n hn
  unfold TwoPointCorrelations.twistByCharacter
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
    (by norm_num)

lemma Multiplicative.twistByCharacter {q : ℕ} {f : ℕ → ℂ}
    (hf : Multiplicative f) (χ : DirichletCharacter ℂ q) :
    Multiplicative (TwoPointCorrelations.twistByCharacter f χ) := by
  intro m n hm hn hcop
  simp only [TwoPointCorrelations.twistByCharacter, hf m n hm hn hcop, Nat.cast_mul, map_mul]
  ring

end TwoPointCorrelations

end OAI
