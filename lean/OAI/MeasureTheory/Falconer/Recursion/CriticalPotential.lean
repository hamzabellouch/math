import OAI.MeasureTheory.Falconer.Recursion.PotentialFrostman

namespace OAI

/-! # The logarithmic potential bound at the critical ball exponent

Unlike the strictly subcritical energy estimate, the finite critical estimate
has one bounded contribution per dyadic scale. It is used on the outer
intervals of the radial profile argument.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_critical (μ : Measure X) (x : X)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  apply (regularized_potential_dyadic μ x hq g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^q)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal K := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^q)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^q)*(1/(2:ℝ)^g)^q) := by ring
          _ = K := by rw [dyadic_potential_start,sub_self,Real.rpow_zero,mul_one]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^q) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*
          ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^q)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = K*(2:ℝ)^q := by
            rw [dyadic_potential_weight,sub_self,Real.rpow_zero,mul_one]
  calc
    _ ≤ ENNReal.ofReal K+∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^q) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = _ := by simp

end Falconer

end OAI
