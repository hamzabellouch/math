import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineKernel
import OAI.Combinatorics.KMedian.Compression.RationalScaling

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def integer (μ : RationalLaw Ω) : IntegerLaw Ω where
  denominator := RationalScaling.denominator μ.weight
  denominator_pos := RationalScaling.denominator_pos μ.weight
  numerator := RationalScaling.numerator μ.weight
  numerator_nonneg i := by
    have hh : (0:ℚ) ≤ (RationalScaling.numerator μ.weight i:ℚ) := by
      rw [RationalScaling.numerator_cast]
      exact mul_nonneg (μ.nonneg i) (by exact_mod_cast (RationalScaling.denominator_pos μ.weight).le)
    exact_mod_cast hh
  total := by
    apply Int.cast_injective (α:=ℚ)
    rw [Int.cast_sum]
    simp only [RationalScaling.numerator_cast,← sum_mul,μ.total,one_mul]

@[simp] theorem integer_weight (μ : RationalLaw Ω) (i : Ω) :
    μ.integer.rational.weight i=μ.weight i := by
  change (RationalScaling.numerator μ.weight i:ℚ)/(RationalScaling.denominator μ.weight:ℚ)=_
  rw [RationalScaling.numerator_cast,mul_div_cancel_right₀]
  exact_mod_cast (RationalScaling.denominator_pos μ.weight).ne'

@[simp] theorem integer_numerator_zero (μ : RationalLaw Ω) (i : Ω) :
    μ.integer.numerator i=0 ↔ μ.weight i=0 := by
  have hD : (RationalScaling.denominator μ.weight:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos μ.weight).ne'
  change RationalScaling.numerator μ.weight i=0 ↔ _
  rw [← Int.cast_eq_zero (α:=ℚ),RationalScaling.numerator_cast,mul_eq_zero,or_iff_left hD]

theorem integer_support_mem (μ : RationalLaw Ω) (i : Ω) :
    i ∈ μ.integer.support ↔ μ.weight i ≠ 0 := by
  rw [IntegerLaw.mem_support]
  exact not_congr (μ.integer_numerator_zero i)

end MetricKMedian.RationalLaw

end OAI
