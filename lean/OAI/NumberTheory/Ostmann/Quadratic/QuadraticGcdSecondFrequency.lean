import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedGcdCorrections
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionNormalization
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionCutoffGeometry

namespace OAI

/-! # The literal second-Poisson correction at one signed frequency -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticGcdSecondFrequency (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (R D e b : ℕ) (u : ℤ) (v w : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D,
    v z.1 * conj (w z.2) *
      (quadraticGaussMultiplier (quadraticPairKernel z.1 z.2) *
        (jacobiSym (u * b) (quadraticPairKernel z.1 z.2) : ℂ) *
        (((M / ((e : ℝ) * Real.sqrt (quadraticPairKernel z.1 z.2)) : ℝ) : ℂ) *
          quadraticSecondDyadicCorrection ρ a ha M H J e (quadraticPairKernel z.1 z.2) b))

theorem quadratic_gcd_second_frequency_split (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} (hM : 0 < M) (H J : ℝ) {R D e b : ℕ}
    (hD : Squarefree D) (ho : Odd D) (he : 0 < e) (hb : 0 < b)
    (u : ℤ) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)
    let w' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)
    let U := quadraticSecondLower (quadraticCorrectionBase M H e b) J
    let V := quadraticSecondUpper (quadraticCorrectionBase M H e b) J
    let L := quadraticSecondWindow J
    quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w =
      (-𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
            (quadraticSqrtNormalize v') (quadraticSqrtNormalize w') b) -
      (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 *
        ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => V < (d : ℝ)),
          ((ArithmeticFunction.moebius d : ℂ) / d) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d v' w' b) +
      (((1 : ℂ) / 2) * ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) *
        (∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) * quadraticMiddleWindow ρ a ha M e N d v' w' b L) := by
  dsimp only
  rw [← quadratic_gcd_low_signed_reindex hD ho v w u b,
    ← quadratic_gcd_high_signed_reindex hD ho v w u b,
    ← quadratic_gcd_middle_correction_reindex ρ a ha hD ho M
      (quadraticSecondLower (quadraticCorrectionBase M H e b) J)
      (quadraticSecondUpper (quadraticCorrectionBase M H e b) J) e b (quadraticSecondWindow J) v w u]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  unfold quadraticGcdSecondFrequency
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hq : 0 < quadraticPairKernel z.1 z.2 := Nat.pos_of_ne_zero
    (quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).ne_zero
  have hn := quadratic_second_correction_normalized ρ a ha hM he hq hb
    (quadraticSecondLower (quadraticCorrectionBase M H e b) J)
    (quadraticSecondUpper (quadraticCorrectionBase M H e b) J) (quadraticSecondWindow J)
  dsimp only [quadraticSecondDyadicCorrection]
  simp only [quadraticCorrectionBase] at hn ⊢
  rw [hn]
  simp only [← Finset.mul_sum]
  push_cast
  ring

end Ostmann

end OAI
