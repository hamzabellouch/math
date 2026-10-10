import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierFrequency

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem subsetAmplifierFrequency_tsum {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι)
    (lam : ℝ) (q : ℕ) (X a : ℝ) :
    (∑' u : ℤ, subsetAmplifierFrequency p hcop S U lam q X a u) =
      (lam : ℂ) ^ U.card *
        @normalizedQuadraticTransform q (∏ i : U, p i) ⟨(subset_modulus_pos p U).ne'⟩
          (subsetCenteredProduct p hcop S U) (q : ZMod (∏ i : U, p i))⁻¹ a ((q : ℝ) / X) := by
  unfold subsetAmplifierFrequency normalizedQuadraticTransform
  rw [tsum_mul_left]
  ring

theorem amplified_transform_eq_frequency {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) {q : ℕ} [NeZero q]
    (hqL : q.Coprime (∏ i, p i)) (hq : Odd q) (hsq : Squarefree q)
    {X : ℝ} (hX : 0 < X) (t : ℤ) :
    (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
      (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
        SchwartzCutoff.psi ((n : ℝ) / X)) / (Real.sqrt X : ℂ) =
      quadraticGaussUnit q * ∑' u : ℤ, amplifierFrequency p hcop S lam q X
        ((t : ℝ) / q + centerCorrection q (∏ i, p i) t) u := by
  classical
  rw [amplified_transform_subset_expansion p hcop S lam q t hX, Finset.sum_div]
  have he (U : Finset ι) :
      ((lam : ℂ) ^ U.card *
        ∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
          subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) *
            SchwartzCutoff.psi ((n : ℝ) / X)) / (Real.sqrt X : ℂ) =
      quadraticGaussUnit q * ∑' u : ℤ, subsetAmplifierFrequency p hcop S U lam q X
        ((t : ℝ) / q + centerCorrection q (∏ i, p i) t) u := by
    let : NeZero (∏ i : U, p i) := ⟨(subset_modulus_pos p U).ne'⟩
    have hc := hqL.of_dvd_right (subset_modulus_dvd p U)
    obtain ⟨r, s, hrs⟩ := exists_crt_bezout hc
    have hp := weighted_poisson_eq_normalized hc hq hsq r s t
      (centerCorrection q (∏ i, p i) t) hrs
      (centerCorrection_divisor hqL (subset_modulus_dvd p U) t) hX
      (subsetCenteredProduct p hcop S U)
    rw [mul_div_assoc, hp, subsetAmplifierFrequency_tsum]
    simp only [Int.cast_natCast]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  symm
  exact Summable.tsum_finsetSum (fun U _ => subsetAmplifierFrequency_summable p hcop S U lam q hX _)

theorem amplified_transform_two_positive {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) {q : ℕ} [NeZero q]
    (hqL : q.Coprime (∏ i, p i)) (hq : Odd q) (hsq : Squarefree q) (hq1 : 1 < q)
    {X : ℝ} (hX : 0 < X) (t : ℤ) :
    ‖∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
      (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
        SchwartzCutoff.psi ((n : ℝ) / X)‖ / Real.sqrt X ≤
      2 * ‖∑' n : ℕ, amplifierFrequency p hcop S lam q X
        ((t : ℝ) / q + centerCorrection q (∏ i, p i) t) ((n : ℤ) + 1)‖ := by
  have he := congrArg norm (amplified_transform_eq_frequency p hcop S lam hqL hq hsq hX t)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    norm_mul, quadraticGaussUnit_norm hq hsq, one_mul] at he
  rw [he]
  exact amplifierFrequency_two_positive p hcop S lam hq1 hX _

end Ostmann.QuadraticCenter

end

end OAI
