import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdSecondFrequency
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullCorrectionReindex

namespace OAI

/-! # The full signed second correction is exactly the three bounded sums -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticGcdSecondTotal (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M H J : ℝ) (R D e K : ℕ) (u : ℤ) (v w : ℕ → ℂ) : ℂ :=
  ∑ b ∈ oddSquarefreeRange K, quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w

theorem quadratic_gcd_second_total_split (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} (hM : 0 < M) (H J : ℝ) {R D e : ℕ}
    (hD : Squarefree D) (ho : Odd D) (he : 0 < e) (K : ℕ)
    (u : ℤ) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)
    let w' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)
    quadraticGcdSecondTotal ρ a ha M H J R D e K u v w =
      (-𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)) *
        quadraticFullLowCorrection M H J e N ((2 * N) ^ 2) K (fun _ _ => True) v' w' -
      (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
        quadraticFullHighCorrection M H J e N ((2 * N) ^ 2) K (fun _ _ => True) v' w' +
      (((1 : ℂ) / 2) * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
        quadraticFullMiddleCorrection ρ a ha M H J e N ((2 * N) ^ 2) K (quadraticSecondWindow J)
          (fun _ _ => True) v' w' := by
  let N := quadraticGcdBlockSize R D
  let v' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D v)
  let w' := quadraticFrequencyTwist u 1 (quadraticGcdBlockCoeff R D w)
  let cL := -𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)
  let cH := ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
    ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)
  let cM := ((1 : ℂ) / 2) * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)
  let lo := fun b => ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ =>
      (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
    (ArithmeticFunction.moebius d : ℂ) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d
      (quadraticSqrtNormalize v') (quadraticSqrtNormalize w') b
  let hi := fun b => ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ =>
      quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)),
    ((ArithmeticFunction.moebius d : ℂ) / d) * quadraticGaussDivisorBilinear (2 * N) (2 * N) d v' w' b
  let mi := fun b => ∑ d ∈ (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d : ℕ =>
      quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
      (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J),
    ((ArithmeticFunction.moebius d : ℂ) / d) *
      quadraticMiddleWindow ρ a ha M e N d v' w' b (quadraticSecondWindow J)
  have hp (b : ℕ) (hb : b ∈ oddSquarefreeRange K) :
      quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w =
        cL * lo b - cH * ((1 / (Real.sqrt b : ℂ)) * hi b) +
          cM * ((1 / (Real.sqrt b : ℂ)) * mi b) := by
    have hs := quadratic_gcd_second_frequency_split (R := R) ρ a ha hM H J hD ho he
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1 u v w
    dsimp only at hs
    dsimp only [cL, cH, cM, lo, hi, mi, N, v', w']
    convert hs using 1; push_cast; ring
  have hsum : quadraticGcdSecondTotal ρ a ha M H J R D e K u v w =
      cL * (∑ b ∈ oddSquarefreeRange K, lo b) -
        cH * (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * hi b) +
        cM * (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * mi b) := by
    unfold quadraticGcdSecondTotal
    rw [show (∑ b ∈ oddSquarefreeRange K, quadraticGcdSecondFrequency ρ a ha M H J R D e b u v w) =
      ∑ b ∈ oddSquarefreeRange K, (cL * lo b - cH * ((1 / (Real.sqrt b : ℂ)) * hi b) +
        cM * ((1 / (Real.sqrt b : ℂ)) * mi b)) from Finset.sum_congr rfl hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  rw [show (∑ b ∈ oddSquarefreeRange K, lo b) = _ from quadratic_full_low_reindex M H J e N _ K v' w',
    show (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * hi b) = _ from
      quadratic_full_high_reindex M H J e N _ K v' w',
    show (∑ b ∈ oddSquarefreeRange K, (1 / (Real.sqrt b : ℂ)) * mi b) = _ from
      quadratic_full_middle_reindex ρ a ha M H J e N _ K (quadraticSecondWindow J) v' w']

end Ostmann

end OAI
