import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonCoefficients
import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonErrors
import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonTruncation

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def coprimePoissonDivisorApprox (ψ : 𝓢(ℝ, ℂ))
    (X Y Z L : ℝ) (d : ℕ) : ℂ :=
  if (d : ℝ) ≤ Z then
    ((X / d : ℝ) : ℂ) * ((∫ x : ℝ, ψ x) +
      if Y < (d : ℝ) then ∑ l ∈ nonzeroIntegerCutoff L, 𝓕 ψ ((l : ℝ) * (X / d)) else 0)
  else ψ 0

noncomputable def coprimePoissonApprox (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (X Y Z L : ℝ) : ℂ :=
  ∑ d ∈ k.divisors, (μ d : ℂ) * coprimePoissonDivisorApprox ψ X Y Z L d

noncomputable def coprimePoissonMain (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (X Y Z L : ℝ) : ℂ :=
  (Nat.totient k : ℂ) / (k : ℂ) * (X : ℂ) * (∫ x : ℝ, ψ x)
  - ψ 0 * (∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Z), (μ d : ℂ))
  - (X : ℂ) * (∫ x : ℝ, ψ x) *
      (∑ d ∈ k.divisors.filter (fun d : ℕ => Z < (d : ℝ)), (μ d : ℂ) / (d : ℂ))
  + (∑ d ∈ k.divisors.filter (fun d : ℕ => Y < (d : ℝ) ∧ (d : ℝ) ≤ Z),
      (μ d : ℂ) * ((X / d : ℝ) : ℂ) *
        (∑ l ∈ nonzeroIntegerCutoff L, 𝓕 ψ ((l : ℝ) * (X / d))))

theorem divisor_lattice_poisson_split (ψ : 𝓢(ℝ, ℂ)) (d : ℕ) (hd : 0 < d)
    (X Y Z L : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ L) :
    (∑' m : ℤ, ψ ((d : ℝ) * m / X)) = coprimePoissonDivisorApprox ψ X Y Z L d
      + (if Z < (d : ℝ) then nonzeroLattice ψ ((d : ℝ) / X) else 0)
      + (if (d : ℝ) ≤ Y then ((X / d : ℝ) : ℂ) * nonzeroLattice (𝓕 ψ) (X / d) else 0)
      + (if Y < (d : ℝ) ∧ (d : ℝ) ≤ Z then
          ((X / d : ℝ) : ℂ) * latticeTail (𝓕 ψ) (X / d) L else 0) := by
  classical
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  have hscaled : (∑' m : ℤ, ψ ((d : ℝ) * m / X)) =
      ∑' m : ℤ, ψ ((m : ℝ) / (X / d)) := by
    apply tsum_congr
    intro m
    congr 1
    field_simp
  by_cases hdZ : (d : ℝ) ≤ Z
  · rw [hscaled]
    by_cases hdY : (d : ℝ) ≤ Y
    · have h := schwartz_poisson_scaled ψ (X / d) (div_pos hX hdr)
      rw [schwartz_lattice_eq_zero_add_nonzero (𝓕 ψ) (X / d) (div_pos hX hdr),
        schwartz_fourier_zero_eq_integral] at h
      simp only [coprimePoissonDivisorApprox, hdZ, hdY, ite_true, not_lt_of_ge hdY, ite_false,
        not_lt_of_ge hdZ, false_and, add_zero]
      linear_combination h
    · have h := schwartz_poisson_scaled_truncated ψ (X / d) (div_pos hX hdr) L hL
      simp only [coprimePoissonDivisorApprox, hdZ, ite_true, lt_of_not_ge hdY, hdY,
        ite_false, not_lt_of_ge hdZ, and_self_iff, add_zero]
      linear_combination h
  · have hdY : ¬ (d : ℝ) ≤ Y := fun h => hdZ (h.trans hYZ)
    have h := schwartz_lattice_eq_zero_add_nonzero ψ ((d : ℝ) / X) (div_pos hdr hX)
    have heq : (∑' m : ℤ, ψ ((m : ℝ) * ((d : ℝ) / X))) =
        ∑' m : ℤ, ψ ((d : ℝ) * m / X) := by
      apply tsum_congr
      intro m
      congr 1
      ring
    rw [heq] at h
    simpa only [coprimePoissonDivisorApprox, hdZ, ite_false, lt_of_not_ge hdZ,
      ite_true, hdY, and_false, add_zero] using h

theorem coprime_lattice_eq_approx_add_errors (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : k ≠ 0)
    (X Y Z L : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ L) :
    (∑' n : ℤ, if Nat.Coprime n.natAbs k then ψ ((n : ℝ) / X) else 0) =
      coprimePoissonApprox ψ k X Y Z L + largeDivisorError ψ k X Z +
        smallDivisorError ψ k X Y + middleDivisorError ψ k X Y Z L := by
  classical
  rw [coprime_lattice_moebius ψ k hk X hX]
  have hsum := Finset.sum_congr rfl (fun d (hd : d ∈ k.divisors) =>
    congrArg (fun z : ℂ => (μ d : ℂ) * z)
      (divisor_lattice_poisson_split ψ d (Nat.pos_of_mem_divisors hd) X Y Z L hX hYZ hL))
  simpa only [coprimePoissonApprox, largeDivisorError, smallDivisorError, middleDivisorError,
    Finset.sum_filter, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib] using hsum

theorem coprimePoissonApprox_eq_main (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 2 ≤ k)
    (X Y Z L : ℝ) : coprimePoissonApprox ψ k X Y Z L = coprimePoissonMain ψ k X Y Z L := by
  classical
  have hsplit : coprimePoissonApprox ψ k X Y Z L =
      (∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Z),
        (μ d : ℂ) * ((X / d : ℝ) : ℂ) * (∫ x : ℝ, ψ x)) +
      (∑ d ∈ k.divisors.filter (fun d : ℕ => Y < (d : ℝ) ∧ (d : ℝ) ≤ Z),
        (μ d : ℂ) * ((X / d : ℝ) : ℂ) *
          (∑ l ∈ nonzeroIntegerCutoff L, 𝓕 ψ ((l : ℝ) * (X / d)))) +
      (∑ d ∈ k.divisors.filter (fun d : ℕ => Z < (d : ℝ)), (μ d : ℂ) * ψ 0) := by
    simp only [coprimePoissonApprox, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdZ : (d : ℝ) ≤ Z <;> by_cases hdY : Y < (d : ℝ) <;>
      simp [coprimePoissonDivisorApprox, hdZ, hdY, not_lt_of_ge, lt_of_not_ge, mul_add] <;> ring
  have hfirst : (∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Z),
      (μ d : ℂ) * ((X / d : ℝ) : ℂ) * (∫ x : ℝ, ψ x)) =
      (X : ℂ) * (∫ x : ℝ, ψ x) *
        (∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Z), (μ d : ℂ) / (d : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    push_cast
    ring
  have hfrac := Finset.sum_filter_add_sum_filter_not
    (s := k.divisors) (p := fun d : ℕ => (d : ℝ) ≤ Z) (f := fun d => (μ d : ℂ) / (d : ℂ))
  simp only [not_le] at hfrac
  rw [sum_moebius_div_divisors k (by omega)] at hfrac
  have hzero := sum_moebius_large_eq_neg_small k hk Z
  rw [hsplit, hfirst, ← Finset.sum_mul, hzero]
  unfold coprimePoissonMain
  linear_combination (X : ℂ) * (∫ x : ℝ, ψ x) * hfrac

end Ostmann.QuadraticSieve

end OAI
