import OAI.NumberTheory.Ostmann.Arithmetic.IntegerFrequencySplit
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTerm
import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplificationWeight
import OAI.NumberTheory.Ostmann.Arithmetic.ScaledPoisson

namespace OAI

/-! # The signed Fourier series and its positive-frequency half -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform
open MeasureTheory

theorem densityFourier_conj {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, conj (f x) = f x) (a : ZMod q) :
    densityFourier f (-a) = conj (densityFourier f a) := by
  simp only [densityFourier, additiveFourier_apply, map_mul, map_sum, map_inv₀,
    map_natCast, Complex.conj_ofReal, stdAddChar_conj, hf, mul_neg, neg_neg]

theorem primeDivisorDensity_conj (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (x : ZMod U.toList.prod) :
    conj (primeDivisorDensity Q hQ D U x) = primeDivisorDensity Q hQ D U x := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [primeDivisorDensity_intCast Q hQ D U hU]
  simp only [map_prod, Complex.conj_ofReal]

/-- Reality of the original physical cutoff supplies Hermitian symmetry of
its Fourier transform without any additional analytic input. -/
theorem fourier_real_conj (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, hf]
  congr 2
  push_cast
  ring

noncomputable def integerQuadraticFrequency {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (M : ℕ) (u : ℤ) : ℂ :=
  (jacobiSym u M : ℂ) * g (a * (u : ZMod q)) *
    realAdditivePhase (θ * (u : ℝ) / q) * Φ ((u : ℝ) / (R * q))

theorem integerQuadraticFrequency_natCast {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (M u : ℕ) :
    integerQuadraticFrequency g a θ Φ R M u =
      (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u := by
  simp only [integerQuadraticFrequency, quadraticFrequencyTerm, realJacobi,
    Int.cast_natCast]
  push_cast
  ring

theorem integerQuadraticFrequency_neg {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (M : ℕ) (hg : ∀ x, g (-x) = conj (g x))
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (u : ℤ) :
    integerQuadraticFrequency g a θ Φ R M (-u) =
      (jacobiSym (-1) M : ℂ) * conj (integerQuadraticFrequency g a θ Φ R M u) := by
  have hj : jacobiSym (-u) M = jacobiSym (-1) M * jacobiSym u M := by
    rw [neg_eq_neg_one_mul, jacobiSym.mul_left]
  simp only [integerQuadraticFrequency, hj, Int.cast_mul, Int.cast_neg, mul_neg,
    neg_div, hg, hΦ, map_mul, ← conj_realAdditivePhase]
  simp only [← Complex.ofReal_intCast, Complex.conj_ofReal]
  ring

theorem integerQuadraticFrequency_split {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (M N : ℕ) (hM : 1 < M) (hR : 0 < R)
    (hg : ∀ x, g (-x) = conj (g x)) (hΦ : ∀ x, Φ (-x) = conj (Φ x))
    (hcut : H * R * q ≤ N) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    (∑' u : ℤ, integerQuadraticFrequency g a θ Φ R M u) =
      (∑ u ∈ Finset.Icc 1 N,
        (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u) +
      (jacobiSym (-1) M : ℂ) * conj (∑ u ∈ Finset.Icc 1 N,
        (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u) := by
  have hh := integer_frequency_conjugate_split
    (integerQuadraticFrequency g a θ Φ R M) N (jacobiSym (-1) M : ℂ)
  simp_rw [integerQuadraticFrequency_natCast] at hh
  apply hh
  · simp only [integerQuadraticFrequency, jacobiSym.zero_left hM,
      Int.cast_zero, zero_mul]
  · intro n
    simpa only [integerQuadraticFrequency_natCast] using
      integerQuadraticFrequency_neg g a θ Φ R M hg hΦ n
  · intro n hn
    rw [quadraticFrequencyTerm_zero_above g a θ Φ R H N n hR hcut hn hsupp, mul_zero]

theorem integerQuadraticFrequency_half_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (M N : ℕ) (hM : 1 < M) (hR : 0 < R)
    (hg : ∀ x, g (-x) = conj (g x)) (hΦ : ∀ x, Φ (-x) = conj (Φ x))
    (hcut : H * R * q ≤ N) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖∑' u : ℤ, integerQuadraticFrequency g a θ Φ R M u‖ ≤
      2 * ‖∑ u ∈ Finset.Icc 1 N,
        (realJacobi u M : ℂ) * quadraticFrequencyTerm g a θ Φ R u‖ := by
  have hh := integer_frequency_norm_le_twice
    (integerQuadraticFrequency g a θ Φ R M) N (jacobiSym (-1) M : ℂ)
  simp_rw [integerQuadraticFrequency_natCast] at hh
  apply hh
  · simp only [integerQuadraticFrequency, jacobiSym.zero_left hM,
      Int.cast_zero, zero_mul]
  · intro n
    simpa only [integerQuadraticFrequency_natCast] using
      integerQuadraticFrequency_neg g a θ Φ R M hg hΦ n
  · intro n hn
    rw [quadraticFrequencyTerm_zero_above g a θ Φ R H N n hR hcut hn hsupp, mul_zero]
  · rcases jacobiSym.trichotomy (-1) M with h | h | h <;> rw [h] <;> norm_num

end Ostmann

end OAI
