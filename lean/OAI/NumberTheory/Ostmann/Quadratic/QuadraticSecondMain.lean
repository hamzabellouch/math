import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondDyadic
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelArithmetic

namespace OAI

/-! # Identifying the first Poisson main term after the square-factor transform -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

theorem quadratic_second_main_normalizer {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) :
    M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b =
      Real.sqrt M / (Real.sqrt e * Real.sqrt b) := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsM := Real.sq_sqrt hM.le
  have hse := Real.sq_sqrt heR.le
  have hsM₀ := (Real.sqrt_pos.mpr hM).ne'
  have hse₀ := (Real.sqrt_pos.mpr heR).ne'
  have hsq₀ := (Real.sqrt_pos.mpr hqR).ne'
  have hsb₀ := (Real.sqrt_pos.mpr hbR).ne'
  unfold quadraticSecondScale
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul heR.le, Real.sqrt_mul hM.le]
  field_simp
  ring_nf
  rw [hsM, hse]
  ring

theorem quadratic_second_main_coefficient {M : ℝ} {q D b : ℕ}
    (hM : 0 < M) (hq : Squarefree q) (ho : Odd q) (hD : Odd D) (hb : 0 < b) :
    quadraticGaussMultiplier q *
      (∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
        (((M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b) : ℝ) : ℂ) *
          ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
            (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
              (Real.sqrt |(a : ℝ)| : ℂ)) =
      (((Real.sqrt M / Real.sqrt b : ℝ) : ℂ)) *
        ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) * quadraticRootCharacter q d := by
  have hq₀ : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  calc
    _ = (((Real.sqrt M / Real.sqrt b : ℝ) : ℂ)) *
        (quadraticGaussMultiplier q *
          (∑ e ∈ (2 * D).divisors,
            ((ArithmeticFunction.moebius e : ℂ) / (Real.sqrt (e : ℝ) : ℂ)) *
              ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
                (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
                  (Real.sqrt |(a : ℝ)| : ℂ))) := by
      conv_rhs => rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [quadratic_second_main_normalizer hM (Nat.pos_of_mem_divisors he) hq₀ hb]
      push_cast
      ring
    _ = _ := by rw [quadratic_fresnel_arithmetic hq ho hD]

end Ostmann

end OAI
