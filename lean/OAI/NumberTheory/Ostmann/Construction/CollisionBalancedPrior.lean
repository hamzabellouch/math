import OAI.NumberTheory.Ostmann.Supply.CollisionPrimeCellBudget
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Balanced mass under the unconditioned harmonic prime prior -/
namespace Ostmann
open scoped Classical BigOperators

theorem primeSubsetPrior_real_mean (P Q : Finset ℕ) (hQP : Q ⊆ P) (f : ℕ → ℝ) :
    (∑ p : P, primeSubsetPrior P Q p * f p) =
      (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * ∑ q ∈ Q, (q : ℝ)⁻¹ * f q := by
  have h := congrArg Complex.re (primeSubsetPrior_mean P Q hQP (fun p => (f p : ℂ)))
  simpa only [← Complex.ofReal_inv, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using h

theorem primeSubsetPrior_balanced_mass (P Q R : Finset ℕ) (hQP : Q ⊆ P) (hRQ : R ⊆ Q)
    (good : ℕ → Prop) [DecidablePred good] (hgood : ∀ p ∈ R, good p)
    (hM : 0 < ∑ p ∈ Q, (p : ℝ)⁻¹)
    (hR : (∑ p ∈ Q, (p : ℝ)⁻¹) / 2 ≤ ∑ p ∈ R, (p : ℝ)⁻¹) :
    (1 / 2 : ℝ) ≤ ∑ p : P, if good p then primeSubsetPrior P Q p else 0 := by
  have he := primeSubsetPrior_real_mean P Q hQP (fun p => if p ∈ R then 1 else 0)
  have hfilter : Q.filter (fun p => p ∈ R) = R := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hRQ h, h⟩⟩
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter] at he
  rw [Finset.sum_filter] at he
  have hnorm : (1 / 2 : ℝ) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ * ∑ p ∈ R, (p : ℝ)⁻¹ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hM]
    linarith
  apply (hnorm.trans_eq he.symm).trans
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : (p : ℕ) ∈ R
  · simpa only [hp, ite_true, hgood p hp] using (le_rfl : primeSubsetPrior P Q p ≤ primeSubsetPrior P Q p)
  · simp only [hp, ite_false]
    split_ifs
    · exact primeSubsetPrior_nonneg P Q p
    · exact le_rfl

theorem collision_harmonic_prior_balanced_mass (P Q ambient : Finset ℕ)
    (hQP : Q ⊆ P) (hQA : Q ⊆ ambient)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (D G : ℝ) (hG : 0 < G)
    (hprime : ∀ p ∈ ambient, p.Prime)
    (hS : ∀ p ∈ ambient, (S p).Nonempty) (hT : ∀ p ∈ ambient, (T p).Nonempty)
    (hcard : ∀ p ∈ ambient, (S p).card + (T p).card = p)
    (hlog : ∀ p ∈ ambient, G ≤ Real.log (p : ℝ))
    (hbudget : (∑ p ∈ ambient, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D)
    (hM : 0 < ∑ p ∈ Q, (p : ℝ)⁻¹)
    (hsmall : 4 * D / G ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) / 2) :
    (1 / 2 : ℝ) ≤ ∑ p : P, if (p : ℝ) / 3 ≤ (S p).card ∧
      ((S p).card : ℝ) ≤ 2 * p / 3 then primeSubsetPrior P Q p else 0 := by
  let E := collisionExceptionalPrimes ambient S T μ ν
  have hEA : E ⊆ ambient := Finset.filter_subset _ _
  have hbad := collisionExceptionalPrimes_log_mass ambient S T μ ν D hprime hS hT
    (fun p hp => (hcard p hp).le) hbudget
  have hbadmass : (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 4 * D / G := by
    apply (le_div_iff₀ hG).mpr
    calc
      _ = ∑ p ∈ E, G * (p : ℝ)⁻¹ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ p ∈ E, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
          (hlog p (hEA hp)) (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ _ := hbad
  have hint : (∑ p ∈ Q ∩ E, (p : ℝ)⁻¹) ≤ ∑ p ∈ E, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => by positivity)
  apply primeSubsetPrior_balanced_mass P Q (Q \ E) hQP Finset.sdiff_subset
    (fun p : ℕ => (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3) ?_ hM ?_
  · intro p hp
    have hh := Finset.mem_sdiff.mp hp
    exact collision_retained_prime_balanced ambient S T μ ν hS hT hcard p
      (Finset.mem_sdiff.mpr ⟨hQA hh.1, hh.2⟩)
  · have he := Finset.sum_inter_add_sum_sdiff Q E (fun p : ℕ => (p : ℝ)⁻¹)
    linarith

end Ostmann

end OAI
