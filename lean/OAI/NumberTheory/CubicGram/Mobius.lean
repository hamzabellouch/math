import Mathlib
import OAI.NumberTheory.CubicGram.SquarefreeGauss

namespace OAI

/-! Ideal Moebius weights and exact prime-factor subset identities. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
def idealMoebius (b : Eisenstein) : ℤ := UniqueFactorizationMonoid.moebius b

lemma idealMoebius_sq (b : Eisenstein) :
    (idealMoebius b : ℝ)^2 = if Squarefree b then 1 else 0 := by
  unfold idealMoebius UniqueFactorizationMonoid.moebius
  split_ifs <;> push_cast
  · rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  · norm_num

theorem norm_gauss_eq_moebius_sq {b : Eisenstein} (hb : primary b) :
    ‖gauss b‖ = (idealMoebius b : ℝ)^2 := by
  rw [norm_gauss hb, idealMoebius_sq]

lemma idealMoebius_mul {a b : Eisenstein} (h : IsCoprime a b) :
    idealMoebius (a*b) = idealMoebius a * idealMoebius b :=
  (isRelPrime_iff_isCoprime.mpr h).moebius_mul

lemma idealMoebius_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    idealMoebius p = -1 := hp.2.irreducible.moebius_eq

lemma idealMoebius_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    idealMoebius (∏ p ∈ s, p) = (-1 : ℤ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [idealMoebius]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, idealMoebius_mul hc, idealMoebius_primaryPrime hp',
      ih hs, Finset.card_insert_of_notMem hps, pow_succ]
    ring

lemma norm_primaryNormalize (p : Eisenstein) : norm (primaryNormalize p) = norm p := by
  simpa only [normNat_cast] using congrArg (fun m : ℕ => (m : ℝ))
    (associated_normNat (primaryNormalize_associated p)).symm

lemma roughProduct_primary_factors (ψ : ℝ → ℝ) (y : ℝ) (n : Eisenstein) :
    roughProduct ψ y n = ∏ p ∈ primaryPrimeFactors n, (1 - ψ (norm p / y)) := by
  rw [primaryPrimeFactors, Finset.prod_image (primaryNormalize_injOn_primeFactors n)]
  simp only [norm_primaryNormalize, roughProduct]

theorem roughProduct_moebius_subsets {n : Eisenstein} (hn : primary n)
    (ψ : ℝ → ℝ) (y : ℝ) :
    roughProduct ψ y n =
      ∑ s ∈ (primaryPrimeFactors n).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℝ) * ∏ p ∈ s, ψ (norm p / y) := by
  rw [roughProduct_primary_factors]
  have hex := Finset.prod_add (fun p : Eisenstein => -ψ (norm p / y))
    (fun _ => (1 : ℝ)) (primaryPrimeFactors n)
  simp only [Finset.prod_const_one, mul_one, ← sub_eq_neg_add] at hex
  rw [hex]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  rw [idealMoebius_prod_primaryPrimes s (fun p hp => (primaryPrimeFactor_spec hn (hsub hp)).1),
    Finset.prod_neg]
  push_cast
  rfl

end CubicFirstMoment
end
end

end OAI
