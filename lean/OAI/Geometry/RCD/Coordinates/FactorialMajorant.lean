import OAI.Geometry.RCD.Coordinates.InverseMajorant
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-!
# Factorial weights for the inverse-jet estimate

We use the fixed admissible Gevrey exponent `σ = 2`.  The weight
`L m = (m + 1) * ((m + 1)!)²` is positive, has `L 0 = 1`, and its
normalized interior convolution tends to zero.  Consequently the
abstract inverse majorant gives one constant for every derivative order.
-/

open Finset Filter
open scoped BigOperators Topology

noncomputable section

namespace RegularPointCoordinates

def factorialMajorant (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * ((m + 1).factorial : ℝ) ^ 2

@[simp] theorem factorialMajorant_zero : factorialMajorant 0 = 1 := by
  norm_num [factorialMajorant]

@[simp] theorem factorialMajorant_one : factorialMajorant 1 = 8 := by
  norm_num [factorialMajorant]

theorem factorialMajorant_pos (m : ℕ) : 0 < factorialMajorant m := by
  unfold factorialMajorant
  positivity

theorem factorialMajorant_succ (m : ℕ) :
    factorialMajorant (m + 1) = ((m : ℝ) + 2) ^ 3 * ((m + 1).factorial : ℝ) ^ 2 := by
  unfold factorialMajorant
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The consecutive ratios of the weight are increasing. -/
theorem factorialMajorant_pair_step {p q : ℕ} (hpq : p ≤ q) :
    factorialMajorant (p + 1) * factorialMajorant q ≤
      factorialMajorant p * factorialMajorant (q + 1) := by
  have hp : (1 : ℝ) ≤ (p : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) p]
  have hq : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) q]
  have hmul := one_le_mul_of_one_le_of_one_le hp hq
  have hlarge : (1 : ℝ) ≤ (p : ℝ) + q + 5 := by linarith
  have hprod := one_le_mul_of_one_le_of_one_le hmul hlarge
  have hd : (0 : ℝ) ≤ (q : ℝ) - p := sub_nonneg.mpr (by exact_mod_cast hpq)
  have hnon := mul_nonneg hd (sub_nonneg.mpr hprod)
  have hpoly : ((p : ℝ) + 2) ^ 3 * ((q : ℝ) + 1) ≤
      ((p : ℝ) + 1) * ((q : ℝ) + 2) ^ 3 := by nlinarith only [hnon]
  have hscaled := mul_le_mul_of_nonneg_right hpoly
    (by positivity : (0 : ℝ) ≤ ((p + 1).factorial : ℝ) ^ 2 *
      ((q + 1).factorial : ℝ) ^ 2)
  rw [factorialMajorant_succ, factorialMajorant_succ]
  unfold factorialMajorant
  convert hscaled using 1 <;> ring

/-- For fixed total order, the largest positive-order product is at an endpoint. -/
theorem factorialMajorant_pair_le_endpoint {l q : ℕ} (hl : 1 ≤ l) (hq : 1 ≤ q) :
    factorialMajorant l * factorialMajorant q ≤
      factorialMajorant 1 * factorialMajorant (l + q - 1) := by
  induction l using Nat.strong_induction_on generalizing q with
  | h l ih =>
    by_cases hlone : l = 1
    · subst l
      simp
    by_cases hlq : l ≤ q
    · have hlprev : 1 ≤ l - 1 := by omega
      have hpq : l - 1 ≤ q := by omega
      have hstep := factorialMajorant_pair_step hpq
      have heq : l - 1 + 1 = l := by omega
      rw [heq] at hstep
      have hbound := ih (l - 1) (by omega) hlprev (by omega : 1 ≤ q + 1)
      have hsum : l - 1 + (q + 1) - 1 = l + q - 1 := by omega
      exact hstep.trans (by simpa only [hsum] using hbound)
    · have hbound := ih q (by omega) hq hl
      simpa only [mul_comm, Nat.add_comm] using hbound

theorem factorialMajorant_endpoint_ratio {m : ℕ} (hm : 1 ≤ m) :
    factorialMajorant 1 * factorialMajorant (m - 1) / factorialMajorant m =
      8 * (m : ℝ) / ((m : ℝ) + 1) ^ 3 := by
  have hm' : m - 1 + 1 = m := by omega
  have hfact : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfactpos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  rw [factorialMajorant_one]
  unfold factorialMajorant
  rw [hm', hfact]
  have hmreal : (m - 1 : ℕ) + (1 : ℝ) = (m : ℝ) := by
    exact_mod_cast hm'
  rw [hmreal]
  field_simp [ne_of_gt hfactpos]

/-- A direct bound sufficient for convolution decay. -/
theorem factorialMajorant_normalized_convolution_le (m : ℕ) :
    normalizedInteriorConvolution factorialMajorant m ≤ 8 / ((m : ℝ) + 1) := by
  by_cases hmzero : m = 0
  · subst m
    norm_num [normalizedInteriorConvolution, interiorConvolution]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmzero
  have hsum : interiorConvolution factorialMajorant m ≤
      (m : ℝ) * (factorialMajorant 1 * factorialMajorant (m - 1)) := by
    calc
      _ ≤ ∑ _l ∈ Finset.Icc 1 (m - 1),
          factorialMajorant 1 * factorialMajorant (m - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' := Finset.mem_Icc.mp hl
        have hq : 1 ≤ m - l := by omega
        have h := factorialMajorant_pair_le_endpoint hl'.1 hq
        have heq : l + (m - l) - 1 = m - 1 := by omega
        simpa only [heq] using h
      _ ≤ (m : ℝ) * (factorialMajorant 1 * factorialMajorant (m - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (factorialMajorant_pos 1).le (factorialMajorant_pos (m - 1)).le)
        have hcard : (Finset.Icc 1 (m - 1)).card ≤ m := by
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hcard
  have hdiv := div_le_div_of_nonneg_right hsum (factorialMajorant_pos m).le
  change normalizedInteriorConvolution factorialMajorant m ≤ _ at hdiv
  calc
    _ ≤ (m : ℝ) * (8 * (m : ℝ) / ((m : ℝ) + 1) ^ 3) := by
      simpa only [mul_div_assoc, factorialMajorant_endpoint_ratio hm] using hdiv
    _ ≤ 8 / ((m : ℝ) + 1) := by
      have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos hp 3) hp]
      nlinarith [sq_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) m]

theorem factorialMajorant_convolution_tendsto_zero :
    Tendsto (normalizedInteriorConvolution factorialMajorant) atTop (𝓝 0) := by
  have hnon (m : ℕ) : 0 ≤ normalizedInteriorConvolution factorialMajorant m :=
    div_nonneg (interiorConvolution_nonneg (fun j => (factorialMajorant_pos j).le) m)
      (factorialMajorant_pos m).le
  have hlim : Tendsto (fun m : ℕ => 8 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 8
    simpa only [mul_zero, mul_one_div] using h
  exact squeeze_zero hnon factorialMajorant_normalized_convolution_le hlim

/-- Restoring the endpoint terms gives the uniform full-convolution estimate. -/
theorem factorialMajorant_full_convolution_le (m : ℕ) :
    (∑ l ∈ Finset.range (m + 1), factorialMajorant l * factorialMajorant (m - l)) ≤
      10 * factorialMajorant m := by
  have hdelta : normalizedInteriorConvolution factorialMajorant m ≤ 8 := by
    apply (factorialMajorant_normalized_convolution_le m).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hinterior : interiorConvolution factorialMajorant m ≤ 8 * factorialMajorant m := by
    have h := mul_le_mul_of_nonneg_right hdelta (factorialMajorant_pos m).le
    rwa [normalizedInteriorConvolution_mul factorialMajorant_pos m] at h
  by_cases hmzero : m = 0
  · subst m
    norm_num
  have hm : 0 < m := Nat.pos_of_ne_zero hmzero
  have hIcc : Finset.Ico 1 m = Finset.Icc 1 (m - 1) := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hsplit : (∑ l ∈ Finset.range (m + 1),
      factorialMajorant l * factorialMajorant (m - l)) =
      2 * factorialMajorant m + interiorConvolution factorialMajorant m := by
    rw [Finset.sum_range_succ,
      Finset.sum_range_eq_add_Ico
        (fun l => factorialMajorant l * factorialMajorant (m - l)) hm, hIcc]
    simp only [Nat.sub_zero, Nat.sub_self, factorialMajorant_zero, one_mul, mul_one]
    unfold interiorConvolution
    ring
  rw [hsplit]
  linarith

/-- The factorial weights satisfy the inverse-coefficient bound with one
constant, uniformly over all orders and all admissible coefficient sequences. -/
theorem factorial_inverse_coefficients_uniform_bound {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, Real.sqrt A ≤ C ∧ 2 * A ≤ C ∧
      ∀ a : ℕ → ℝ, a 0 ≤ Real.sqrt A →
        HasInverseMajorantRecurrence factorialMajorant a A →
        ∀ m, a m ≤ C * factorialMajorant m :=
  inverse_coefficients_uniform_bound factorialMajorant_pos factorialMajorant_zero hA
    factorialMajorant_convolution_tendsto_zero

end RegularPointCoordinates

end

end OAI
