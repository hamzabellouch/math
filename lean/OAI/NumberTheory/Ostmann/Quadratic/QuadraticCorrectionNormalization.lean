import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstSecondMain

namespace OAI

/-! # The three original divisor weights after Gauss normalization -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_scaled_divisor_sum (S : Finset ℕ) (X : ℝ) (F : ℕ → ℂ) :
    (∑ d ∈ S, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * F d) =
      (X : ℂ) * ∑ d ∈ S, ((ArithmeticFunction.moebius d : ℂ) / d) * F d := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

theorem quadratic_second_correction_normalized (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e q b : ℕ} (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b)
    (U V : ℝ) (L : ℕ) :
    (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)) *
      quadraticSecondCorrection q ρ a ha (quadraticSecondScale M e q b) U V L =
    -(((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)) / 2 * 𝓕 ρ 0 *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) -
    (((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) / 2 *
      ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d) +
    (((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)) / 2 *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
        ((ArithmeticFunction.moebius d : ℂ) / d) *
          quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha))
            (quadraticSecondScale M e q b / d) L) := by
  let X := quadraticSecondScale M e q b
  let α : ℂ := ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)
  let β : ℂ := ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)
  have hn : α * (X : ℂ) = β := by
    dsimp [α, β, X]
    rw [← Complex.ofReal_mul, quadratic_second_main_normalizer hM he hq hb]
  have hh : (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) =
      (X : ℂ) * ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) / d := by
    simpa only [mul_one] using quadratic_scaled_divisor_sum
      (q.divisors.filter (fun d : ℕ => V < (d : ℝ))) X (fun _ => 1)
  have hm := quadratic_scaled_divisor_sum
    (q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V)) X
    (fun d => quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L)
  change α * quadraticSecondCorrection q ρ a ha X U V L = _
  unfold quadraticSecondCorrection
  rw [hh, hm]
  calc
    _ = -α / 2 * 𝓕 ρ 0 *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) -
      (α * (X : ℂ)) / 2 *
        ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) * ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d) +
      (α * (X : ℂ)) / 2 *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) *
            quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) := by ring
    _ = _ := by rw [hn]

end Ostmann

end OAI
