import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondMain

namespace OAI

/-! # The three retained divisor corrections with their original normalization -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_second_core_normalized (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    {M : ℝ} {e q b : ℕ} (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b)
    (U V : ℝ) (L : ℕ) :
    let X := quadraticSecondScale M e q b
    let R : ℂ := ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)
    let P : ℂ := (quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)
    ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSecondPoissonCore q ρ a ha X U V L =
      R / 2 * (((q.totient : ℂ) / q) * P -
        P * (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) / d) +
        ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
          ((ArithmeticFunction.moebius d : ℂ) / d) *
            quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) -
      (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) / 2) * 𝓕 ρ 0 *
        (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius d : ℂ)) := by
  dsimp only
  let X := quadraticSecondScale M e q b
  let S : ℂ := ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ)
  let R : ℂ := ((Real.sqrt M / (Real.sqrt e * Real.sqrt b) : ℝ) : ℂ)
  have hn : S * (X : ℂ) = R := by
    dsimp [S, X, R]
    rw [← Complex.ofReal_mul, quadratic_second_main_normalizer hM he hq hb]
  have hsum (F : Finset ℕ) (g : ℕ → ℂ) :
      S * (∑ d ∈ F, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * g d) =
        R * ∑ d ∈ F, ((ArithmeticFunction.moebius d : ℂ) / d) * g d := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    calc
      _ = (S * (X : ℂ)) * (((ArithmeticFunction.moebius d : ℂ) / d) * g d) := by ring
      _ = _ := by rw [hn]
  have hlarge : S * (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) =
      R * ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) / d := by
    simpa only [mul_one] using hsum (q.divisors.filter (fun d : ℕ => V < (d : ℝ))) (fun _ => 1)
  have hmiddle := hsum
    (q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V))
    (fun d => quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L)
  change S * quadraticSecondPoissonCore q ρ a ha X U V L = _
  unfold quadraticSecondPoissonCore
  have hmain (P : ℂ) : S * (((X : ℂ) * q.totient / q) * P) =
      R * ((q.totient : ℂ) / q) * P := by
    calc
      _ = (S * (X : ℂ)) * ((q.totient : ℂ) / q) * P := by ring
      _ = _ := by rw [hn]
  have hdist (x l p h k : ℂ) :
      S * ((x - l - p * h + k) / 2) =
        (S * x - S * l - p * (S * h) + S * k) / 2 := by ring
  rw [hdist, hmain, hlarge, hmiddle]
  dsimp only [S, R, X]
  ring

end Ostmann

end OAI
