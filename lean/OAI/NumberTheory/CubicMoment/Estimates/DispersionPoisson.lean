import OAI.NumberTheory.CubicMoment.Estimates.DispersionExpansion
import OAI.NumberTheory.CubicGram.CubicOperator

namespace OAI

/-!
# The exact arithmetic identity for dispersion

The existing lattice Poisson theorem is applied to the actual Gauss-sum
rows. Conjugation reverses the mixed-character pair; the two normalized
Gauss factors then cancel. The resulting identity retains the dispersion remainder explicitly.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def smoothedDispersionVariance (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then
    W (norm a / A) * ((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0

theorem dispersionPolynomial_conj (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) :
    dispersionPolynomial B β u a =
      star (∑ b ∈ B, star (dispersionAmplitude β u b) * cubicSymbol b a) := by
  simp only [dispersionPolynomial, star_sum, star_mul, star_star, dispersionAmplitude, mul_comm]

/-- The full lattice variance is precisely a finite quadratic form in
primary character Gram entries. -/
theorem smoothedDispersionVariance_gram (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance B β u W A =
      ∑ p ∈ B, ∑ q ∈ B, dispersionAmplitude β u p * star (dispersionAmplitude β u q) *
        primaryCharacterGram q p W A := by
  have he : smoothedDispersionVariance B β u W A =
      primarySmoothedSieveMass B (fun b => star (dispersionAmplitude β u b)) W A := by
    unfold smoothedDispersionVariance primarySmoothedSieveMass
    apply tsum_congr
    intro a
    rw [dispersionPolynomial_conj, norm_star]
  rw [he, primarySmoothedSieveMass_gram B hB _ W hW hW' hA, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  simp only [star_star]
  ring

theorem primaryCharacterGram_self {b : Eisenstein} (hb : primary b)
    (W : ℝ → ℂ) (A : ℝ) :
    primaryCharacterGram b b W A =
      ∑' a : Eisenstein, if primary a ∧ IsCoprime b a then W (norm a/A) else 0 := by
  unfold primaryCharacterGram
  apply tsum_congr
  intro a
  by_cases ha : primary a
  · simp only [ha, true_and, ite_true]
    by_cases hba : IsCoprime b a
    · have hc : cubicSymbol b a * star (cubicSymbol b a) = 1 := by
        have h := Complex.mul_conj' (cubicSymbol b a)
        simp only [starRingEnd_apply, norm_cubicSymbol_of_isCoprime hb hba] at h
        simpa using h
      rw [ite_eq_left hba, mul_assoc, hc, mul_one]
    · simp [hba, cubicSymbol_eq_zero_of_not_isCoprime hb hba]
  · simp [ha]

theorem dispersionAmplitude_mul_star {b : Eisenstein} (hb : primary b)
    (hsb : Squarefree b) (β : Eisenstein → ℂ) (u : ℝ) :
    dispersionAmplitude β u b * star (dispersionAmplitude β u b) = ((‖β b‖^2 : ℝ) : ℂ) := by
  have h := Complex.mul_conj' (dispersionAmplitude β u b)
  simp only [starRingEnd_apply] at h
  rw [h]
  simp only [dispersionAmplitude, norm_mul, norm_normTwist, mul_one, norm_gauss hb,
    ite_eq_left hsb, Complex.ofReal_pow]

/-- The exact diagonal retains the coprimality condition in the lattice count. -/
theorem dispersion_diagonal (B : Finset Eisenstein) (hB : ∀ b ∈ B, primary b)
    (hsB : ∀ b ∈ B, Squarefree b) (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    (∑ b ∈ B, dispersionAmplitude β u b * star (dispersionAmplitude β u b) *
      primaryCharacterGram b b W A) =
      ∑ b ∈ B, ((‖β b‖^2 : ℝ) : ℂ) *
        ∑' a : Eisenstein, if primary a ∧ IsCoprime b a then W (norm a/A) else 0 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [dispersionAmplitude_mul_star (hB b hb) (hsB b hb), primaryCharacterGram_self (hB b hb)]

/-- For a coprime pair, the normalized Gauss factors cancel against those
in the lattice Poisson formula, leaving the explicit character frequency sum. -/
theorem dispersion_pair_poisson {p q : Eisenstein}
    (hp : primary p) (hq : primary q) (hsp : Squarefree p) (hsq : Squarefree q)
    (hpq : IsCoprime p q) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    dispersionAmplitude β u p * star (dispersionAmplitude β u q) *
      primaryCharacterGram q p W A =
      β p * star (β q) * normTwist u p * star (normTwist u q) *
        ((A / (9 * Real.sqrt (norm (q*p))) : ℝ) : ℂ) *
          ∑' h : Eisenstein, gramDualTerm q p W A h := by
  rw [primaryCharacterGram_poisson_normalized hq hp hsq hsp hpq.symm W hW hW' hA]
  have hg₁ : gauss p * star (gauss p) = 1 := by
    simpa only [ite_eq_left hsp] using gauss_mul_star_squarefree hp
  have hg₂ : gauss q * star (gauss q) = 1 := by
    simpa only [ite_eq_left hsq] using gauss_mul_star_squarefree hq
  simp only [dispersionAmplitude, star_mul]
  calc
    _ = (β p * star (β q) * normTwist u p * star (normTwist u q) *
          ((A / (9 * Real.sqrt (norm (q*p))) : ℝ) : ℂ) *
            ∑' h : Eisenstein, gramDualTerm q p W A h) *
          (gauss p * star (gauss p)) * (gauss q * star (gauss q)) := by ring
    _ = _ := by rw [hg₁, hg₂, mul_one, mul_one]

/-- Exact separation of the diagonal from the off-diagonal quadratic form. -/
theorem smoothedDispersionVariance_split (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (hsB : ∀ b ∈ B, Squarefree b)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance B β u W A =
      (∑ b ∈ B, ((‖β b‖^2 : ℝ) : ℂ) *
        ∑' a : Eisenstein, if primary a ∧ IsCoprime b a then W (norm a/A) else 0) +
      ∑ p ∈ B, ∑ q ∈ B.erase p,
        dispersionAmplitude β u p * star (dispersionAmplitude β u q) *
          primaryCharacterGram q p W A := by
  rw [smoothedDispersionVariance_gram B hB β u W hW hW' hA,
    ← dispersion_diagonal B hB hsB β u W A, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact (Finset.add_sum_erase B _ hp).symm

end CubicFirstMoment

end

end OAI
