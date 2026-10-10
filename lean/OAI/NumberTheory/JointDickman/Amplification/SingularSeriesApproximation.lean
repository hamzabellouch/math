import OAI.NumberTheory.JointDickman.Counting.SingularSeriesPeriodic
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Periodic approximation of the singular series in arithmetic mean -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def totientSquareSum : ℝ := ∑' q : ℕ, 1/(q.totient : ℝ)^2

theorem totientSquareSum_nonneg : 0 ≤ totientSquareSum :=
  tsum_nonneg (fun _ => by positivity)

theorem singularSeries_partial_abs_bound
    (hMP : PublishedInputs.PrimeProductMertensInput) (n Q : ℕ) :
    |∑ q ∈ range Q, singularSeriesCoefficient n q| ≤ totientSquareSum := by
  calc
    _ ≤ ∑ q ∈ range Q, |singularSeriesCoefficient n q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ range Q, 1/(q.totient : ℝ)^2 := sum_le_sum (fun q _ => by
      simpa only [Real.norm_eq_abs] using singularSeriesCoefficient_norm_le n q)
    _ ≤ totientSquareSum := (summable_totient_reciprocal_sq hMP).sum_le_tsum _
      (fun _ _ => by positivity)

theorem singularSeries_periodic_error (hMP : PublishedInputs.PrimeProductMertensInput)
    (Y Q n : ℕ) :
    |singularSeries n-periodicSingularSeries Y Q n| ≤
      ((n : ℝ)/n.totient)*singularSeriesTail Q +
        |(n : ℝ)/n.totient-totientLocalProduct Y n| *totientSquareSum := by
  let r : ℝ := (n : ℝ)/n.totient
  let a : ℝ := ∑' q, singularSeriesCoefficient n q
  let b : ℝ := ∑ q ∈ range Q, singularSeriesCoefficient n q
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : |a-b| ≤ singularSeriesTail Q := by
    simpa only [Real.norm_eq_abs] using singularSeries_tail_bound hMP n Q
  change |r*a-totientLocalProduct Y n*b| ≤ _
  calc
    _ = |r*(a-b)+(r-totientLocalProduct Y n)*b| := by congr 1; ring
    _ ≤ |r*(a-b)|+|(r-totientLocalProduct Y n)*b| := abs_add_le _ _
    _ = r*|a-b|+|r-totientLocalProduct Y n| *|b| := by rw [abs_mul,abs_mul,abs_of_nonneg hr]
    _ ≤ r*singularSeriesTail Q+|r-totientLocalProduct Y n| *totientSquareSum :=
      add_le_add (mul_le_mul_of_nonneg_left ht hr)
        (mul_le_mul_of_nonneg_left (singularSeries_partial_abs_bound hMP n Q) (abs_nonneg _))

theorem totient_ratio_mean_bound (U : ℕ) :
    (∑ n ∈ Ioc 0 U, (n : ℝ)/n.totient) ≤ Real.exp 24*U := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 U, singularFactor 24 n := sum_le_sum (fun n hn =>
      totient_ratio_le_singularFactor (mem_Ioc.mp hn).1)
    _ ≤ Real.exp 24*U := by
      simpa using singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 U

theorem singularSeries_periodic_mean_error
    (hMP : PublishedInputs.PrimeProductMertensInput) (Y Q U : ℕ) (hY : 0 < Y) :
    (∑ n ∈ Ioc 0 U, |singularSeries n-periodicSingularSeries Y Q n|) ≤
      (Real.exp 24*singularSeriesTail Q+(2*Real.exp 2*totientSquareSum)/(Y : ℝ))*U := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 U, (((n : ℝ)/n.totient)*singularSeriesTail Q+
        |(n : ℝ)/n.totient-totientLocalProduct Y n| *totientSquareSum) :=
      sum_le_sum (fun n _ => singularSeries_periodic_error hMP Y Q n)
    _ = (∑ n ∈ Ioc 0 U, (n : ℝ)/n.totient)*singularSeriesTail Q+
        (∑ n ∈ Ioc 0 U, |(n : ℝ)/n.totient-totientLocalProduct Y n|)*totientSquareSum := by
      rw [sum_add_distrib,sum_mul,sum_mul]
    _ ≤ (Real.exp 24*U)*singularSeriesTail Q+
        ((2*Real.exp 2)*(U : ℝ)/Y)*totientSquareSum :=
      add_le_add (mul_le_mul_of_nonneg_right (totient_ratio_mean_bound U)
        (singularSeriesTail_nonneg Q))
        (mul_le_mul_of_nonneg_right (totientLocalProduct_mean_error Y U hY) totientSquareSum_nonneg)
    _ = _ := by ring

/-- The finite period is fixed before the averaging length. -/
theorem singularSeries_periodic_approximation
    (hMP : PublishedInputs.PrimeProductMertensInput) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℕ) (_ : NeZero q) (F : ZMod q → ℝ),
      ∀ U : ℕ, (∑ n ∈ Ioc 0 U, |singularSeries n-F (n : ZMod q)|) ≤ ε*U := by
  have hlim : Tendsto (fun N : ℕ => Real.exp 24*singularSeriesTail N+
      (2*Real.exp 2*totientSquareSum)/(N : ℝ)) atTop (𝓝 0) := by
    simpa using (singularSeriesTail_tendsto_zero.const_mul (Real.exp 24)).add
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2*Real.exp 2*totientSquareSum))
  obtain ⟨N,hN,hsmall⟩ := (eventually_ge_atTop 1 |>.and
    (hlim.eventually (eventually_lt_nhds hε))).exists
  let q := N.factorial
  have hq : NeZero q := ⟨Nat.factorial_ne_zero N⟩
  let := hq
  refine ⟨q,hq,fun r => periodicSingularSeries N N r.val,?_⟩
  intro U
  have he (n : ℕ) : periodicSingularSeries N N (n : ZMod q).val =
      periodicSingularSeries N N n := by
    apply periodicSingularSeries_modEq
    simpa only [max_self,ZMod.val_natCast] using Nat.mod_modEq n q
  simp_rw [he]
  exact (singularSeries_periodic_mean_error hMP N N U (by omega)).trans
    (mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg U))

end JointDickman

end OAI
