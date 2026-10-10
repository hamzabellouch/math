import OAI.NumberTheory.EgyptianFractions.VaughanTypeI
import OAI.NumberTheory.EgyptianFractions.RealTypeI

namespace OAI
/-!
# Actual near-rational estimates for the two Vaughan Type I terms

The prefix adapter uses the sharper canonical harmonic hyperbola bound
for its scalar aggregation.
The variable hyperbolic lengths are retained throughout.  In particular the
right hand side has size `N / q + A + q`, up to logarithmic factors, rather
than the much larger fixed-cap estimate obtained by replacing every `N / d`
with `N`.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.VaughanHyperbolic

open Vaughan

open RationalPhaseSpacing

/-- Every hyperbolic inner prefix has the required variable-cap envelope.
This includes the zero-frequency case and does not require a nonresonance
assumption. -/
theorem norm_phase_Ioc_mul_le_variable (α : ℝ) (N d k : ℕ) (hk : k ≤ N / d) :
    ‖∑ b ∈ Finset.Ioc 0 k, RealPhase.phase (α * (d * b : ℕ))‖ ≤
      truncatedInv ((N : ℝ) / d) (intDistance (α * d)) := by
  have heq : (∑ b ∈ Finset.Ioc 0 k, RealPhase.phase (α * (d * b : ℕ))) =
      ∑ j ∈ Finset.range k, RealPhase.phase ((α * d) * (1 + j) + 0) := by
    rw [sum_Ioc_zero_eq_sum_range_succ]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    push_cast
    ring
  rw [heq]
  exact (RealPhase.norm_sum_shift_phase_le_envelope (α * d) 0 1 k).trans
    (RealTypeI.geometric_envelope_le_truncated_real (α * d) k ((N : ℝ) / d)
      ((by exact_mod_cast hk : (k : ℝ) ≤ (N / d : ℕ)).trans Nat.cast_div_le))

/-- The positive-initial-interval convention used by Vaughan's identity. -/
theorem sum_variable_reciprocal_Ioc_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N A : ℕ) :
    (∑ d ∈ Finset.Ioc 0 A,
      truncatedInv ((N : ℝ) / d) (intDistance (α * d))) ≤
      RealTypeI.hyperbolicCost (N : ℝ) A q := by
  have hcast : (∑ d ∈ Finset.Ioc 0 A,
      truncatedInv ((N : ℝ) / d) (intDistance (α * d))) =
      ∑ d ∈ Finset.Icc 1 (A : ℤ),
        truncatedInv ((N : ℝ) / d) (intDistance (α * d)) := by
    apply Finset.sum_nbij' (fun d : ℕ => (d : ℤ)) Int.toNat
    · intro d hd
      obtain ⟨hd0, hdA⟩ := Finset.mem_Ioc.mp hd
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hd0, by exact_mod_cast hdA⟩
    · intro d hd
      obtain ⟨hd1, hdA⟩ := Finset.mem_Icc.mp hd
      apply Finset.mem_Ioc.mpr
      omega
    · intro d hd
      exact Int.toNat_natCast d
    · intro d hd
      exact Int.toNat_of_nonneg (by have := (Finset.mem_Icc.mp hd).1; omega)
    · intro d hd
      simp
  rw [hcast]
  exact sum_truncatedInv_hyperbolic_le α a q hq hcop happrox N (Nat.cast_nonneg N) A

/-- The first actual Vaughan convolution, with its logarithmic inner weight,
is bounded using only a reduced rational approximation to the frequency. -/
theorem first_typeI_real_phase_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U : ℕ) :
    ‖weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      2 * Real.log N * RealTypeI.hyperbolicCost (N : ℝ) (min U N) q := by
  apply (first_typeI_bound (fun n => RealPhase.phase (α * n)) N U
    (fun d => truncatedInv ((N : ℝ) / d) (intDistance (α * d)))
    (fun d _ k hk => norm_phase_Ioc_mul_le_variable α N d k hk)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_variable_reciprocal_Ioc_le α a q hq hcop happrox N (min U N))
    (by positivity)

/-- The second actual Vaughan convolution has one logarithmic coefficient
factor and the same variable-length reciprocal budget. -/
theorem second_typeI_real_phase_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V : ℕ) :
    ‖weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (typeICoefficient U V * ζ)‖ ≤
      Real.log N * RealTypeI.hyperbolicCost (N : ℝ) (min (U * V) N) q := by
  apply (second_typeI_bound (fun n => RealPhase.phase (α * n)) N U V
    (fun d => truncatedInv ((N : ℝ) / d) (intDistance (α * d)))
    (fun d _ => norm_phase_Ioc_mul_le_variable α N d (N / d) le_rfl)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_variable_reciprocal_Ioc_le α a q hq hcop happrox N (min (U * V) N))
    (Real.log_natCast_nonneg N)

end Problem337.VaughanHyperbolic

end

end OAI
