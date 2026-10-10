import OAI.NumberTheory.CubicMoment.Estimates.PrimeIdealBall
import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters

namespace OAI

/-! Exact deletion of finitely many Euler factors in prime-ideal sums.
Its logarithmic cost is bounded by the norm of the original modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeIdealRestriction (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (ν : EisensteinIdealExponent) : ℂ :=
  if ∀ p ∈ S, ν p=0 then χ ν else 0

lemma primeIdealRestriction_single (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (p : EisensteinIdealPrime) :
    primeIdealRestriction S χ (Finsupp.single p 1) =
      if p ∈ S then 0 else χ (Finsupp.single p 1) := by
  have he : (∀ q ∈ S, (Finsupp.single p 1 : EisensteinIdealExponent) q=0) ↔ p ∉ S := by
    constructor
    · intro h hp
      have hh := h p hp
      simp at hh
    · intro hp q hq
      have hqp : q ≠ p := fun he => hp (he ▸ hq)
      simp [hqp]
  unfold primeIdealRestriction
  by_cases hp : p ∈ S
  · rw [ite_eq_right (fun h => (he.mp h) hp),ite_eq_left hp]
  · rw [ite_eq_left (he.mpr hp),ite_eq_right hp]

theorem primeIdeal_restriction_error (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (X : ℝ) :
    ‖idealPrimeChebyshev χ X-idealPrimeChebyshev (primeIdealRestriction S χ) X‖ ≤
      ∑ p ∈ S, Real.log (idealExponentNorm (Finsupp.single p 1)) := by
  rw [idealPrimeChebyshev_eq_sum_primes,idealPrimeChebyshev_eq_sum_primes,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primeIdealBall X, if p ∈ S then
        Real.log (idealExponentNorm (Finsupp.single p 1)) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      rw [primeIdealRestriction_single]
      by_cases hmem : p ∈ S
      · simp only [hmem,ite_true]
        rw [mul_zero,sub_zero,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (primeIdealLog_nonneg p)]
        exact mul_le_of_le_one_right (primeIdealLog_nonneg p) (hχ _)
      · simp only [hmem,ite_false,sub_self,norm_zero,le_refl]
    _ = ∑ p ∈ (primeIdealBall X).filter (fun p => p ∈ S),
        Real.log (idealExponentNorm (Finsupp.single p 1)) := by rw [Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p _ _ => primeIdealLog_nonneg p)

theorem primeIdeal_restriction_norm_cost (ν : EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ κ, ‖χ κ‖ ≤ 1) (X : ℝ) :
    ‖idealPrimeChebyshev χ X-idealPrimeChebyshev (primeIdealRestriction ν.support χ) X‖ ≤
      Real.log (idealExponentNorm ν) :=
  (primeIdeal_restriction_error ν.support χ hχ X).trans
    (primeIdealLog_sum_le ν.support ν (Finset.Subset.refl _))

theorem induced_residue_prime_error {q d : Eisenstein} (hq : q ≠ 0) (hd : d ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (X : ℝ) :
    ‖idealPrimeChebyshev (residueIdealChar q χ) X-
      idealPrimeChebyshev (residueIdealChar d ψ) X‖ ≤ Real.log (norm q) := by
  have he : residueIdealChar q χ = primeIdealRestriction (idealExponentOf q).support (residueIdealChar d ψ) :=
    funext (induced_residueIdealChar hq h)
  rw [he,norm_sub_rev]
  have hh := primeIdeal_restriction_norm_cost (idealExponentOf q)
    (residueIdealChar d ψ) (residueIdealChar_norm_le_one hd ψ) X
  rwa [idealExponentOf_norm hq] at hh

end CubicFirstMoment

end

end OAI
