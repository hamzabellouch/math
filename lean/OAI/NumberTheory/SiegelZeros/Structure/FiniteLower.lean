import OAI.NumberTheory.SiegelZeros.Determinants.ThetaDivisibility
import OAI.NumberTheory.SiegelZeros.Estimates.FloorExponents
import OAI.NumberTheory.SiegelZeros.Estimates.PrimeBounds

namespace OAI

namespace SiegelZeros


open scoped NumberField

namespace W08

variable {K : Type*} [Field K] [NumberField K]

theorem quartic_norm_finite_lower {ι : Type*} (rows : Finset ι) (order : ι → ℕ)
    {U : ℝ} (good : Finset ℕ) (hsub : good ⊆ primesUpTo U)
    (hdegree : Module.finrank ℚ K = 4) (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (hdiv : ∀ p ∈ good, (p : 𝓞 K) ^ W44.exponent rows order p ∣ Δ) :
    (∑ i ∈ rows, (order i : ℝ)) * (∑ p ∈ good, Real.log (p : ℝ) / p) -
      rows.card * (∑ p ∈ primesUpTo U, Real.log (p : ℝ)) ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℤ Δ : ℝ)| := by
  have hp : ∀ p ∈ primesUpTo U, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  exact (W44.logarithmic_exponent_lower_subset rows order good (primesUpTo U)
    hsub (fun p hp' => (hp p hp').one_le)).trans
      (WeightedTorusJets.W45.quartic_integral_norm_log_lower hdegree good
        (W44.exponent rows order) Δ hΔ (fun p hp' => hp p (hsub hp')) hdiv)

theorem quartic_norm_lower_of_prime_mass {ι : Type*} (rows : Finset ι)
    (order : ι → ℕ) {U L : ℝ} (hU : 0 ≤ U) (good : Finset ℕ)
    (hsub : good ⊆ primesUpTo U)
    (hmass : L ≤ ∑ p ∈ good, Real.log (p : ℝ) / p)
    (hdegree : Module.finrank ℚ K = 4) (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (hdiv : ∀ p ∈ good, (p : 𝓞 K) ^ W44.exponent rows order p ∣ Δ) :
    (∑ i ∈ rows, (order i : ℝ)) * L - Real.log 4 * rows.card * U ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℤ Δ : ℝ)| := by
  have hfinite := quartic_norm_finite_lower rows order good hsub hdegree Δ hΔ hdiv
  have hs : 0 ≤ ∑ i ∈ rows, (order i : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hmass' := mul_le_mul_of_nonneg_left hmass hs
  have hcheb := mul_le_mul_of_nonneg_left (sum_prime_log_le hU)
    (Nat.cast_nonneg rows.card : (0 : ℝ) ≤ rows.card)
  nlinarith

theorem quartic_norm_source_finitelower {ι : Type*} (rows : Finset ι)
    (order : ι → ℕ) {U ell delta C CH : ℝ} (hU : 0 ≤ U) (good : Finset ℕ)
    (hsub : good ⊆ primesUpTo U)
    (hmass : Real.log U - C * ell - C * delta * Real.log U ^ 2 / ell - CH ≤
      ∑ p ∈ good, Real.log (p : ℝ) / p)
    (hdegree : Module.finrank ℚ K = 4) (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (hdiv : ∀ p ∈ good, (p : 𝓞 K) ^ W44.exponent rows order p ∣ Δ) :
    (∑ i ∈ rows, (order i : ℝ)) *
        (Real.log U - C * ell - C * delta * Real.log U ^ 2 / ell - CH) -
      Real.log 4 * rows.card * U ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℤ Δ : ℝ)| :=
  quartic_norm_lower_of_prime_mass rows order hU good hsub hmass hdegree Δ hΔ hdiv

end W08


end SiegelZeros

end OAI
