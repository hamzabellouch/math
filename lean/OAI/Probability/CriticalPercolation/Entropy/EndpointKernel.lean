import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.FiniteEntropy

lemma integral_polynomial_sum (n : ℕ) (c : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, ∑ i ∈ Finset.range n, c i * t^i) =
      ∑ i ∈ Finset.range n, c i / ((i:ℝ)+1) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ => c i * t^i)).intervalIntegrable 0 1

lemma integral_cubic_square (a b c d : ℝ) :
    (∫ t in (0:ℝ)..1, (a + b*t + c*t^2 + d*t^3)^2) =
      a^2 + a*b + (b^2+2*a*c)/3 + (2*a*d+2*b*c)/4 +
        (c^2+2*b*d)/5 + (2*c*d)/6 + d^2/7 := by
  have hpoly (t : ℝ) : (a+b*t+c*t^2+d*t^3)^2 =
      ∑ i ∈ Finset.range 7, (![a^2, 2*a*b, b^2+2*a*c, 2*a*d+2*b*c,
        c^2+2*b*d, 2*c*d, d^2] : Fin 7 → ℝ) ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩ * t^i := by
    simp [Finset.sum_range_succ]
    ring
  simp_rw [hpoly]
  rw [integral_polynomial_sum]
  simp [Finset.sum_range_succ]
  ring

theorem cubic_endpoint (a b c d : ℝ) :
    a^2 ≤ 16 * ∫ t in (0:ℝ)..1, (a+b*t+c*t^2+d*t^3)^2 := by
  rw [integral_cubic_square]
  let z₀ := a+b/2+c/3+d/4
  let z₁ := -(b/2+c/2+9*d/20)/3
  let z₂ := (c/6+d/4)/5
  let z₃ := -(d/20)/7
  have hid : 16*(a^2+a*b+(b^2+2*a*c)/3+(2*a*d+2*b*c)/4+
      (c^2+2*b*d)/5+(2*c*d)/6+d^2/7)-a^2 =
      3*(z₀-z₁)^2+5*(z₀-z₂)^2+7*(z₀-z₃)^2+
        15*(z₁-z₂)^2+21*(z₁-z₃)^2+35*(z₂-z₃)^2 := by
    dsimp [z₀, z₁, z₂, z₃]
    ring
  have : 0 ≤ 16*(a^2+a*b+(b^2+2*a*c)/3+(2*a*d+2*b*c)/4+
      (c^2+2*b*d)/5+(2*c*d)/6+d^2/7)-a^2 := by
    rw [hid]
    positivity
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy

def endpointKernel (t : ℝ) : ℝ := 16 - 120*t + 240*t^2 - 140*t^3

lemma continuous_endpointKernel : Continuous endpointKernel := by
  unfold endpointKernel
  fun_prop

lemma integral_endpointKernel_sq :
    (∫ t in (0:ℝ)..1, (endpointKernel t)^2) = 16 := by
  have he (t : ℝ) : endpointKernel t = 16 + (-120)*t + 240*t^2 + (-140)*t^3 := by
    unfold endpointKernel; ring
  simp_rw [he]
  rw [integral_cubic_square]
  norm_num

lemma integral_endpointKernel_power {k : ℕ} (hk : k ≤ 3) :
    (∫ t in (0:ℝ)..1, endpointKernel t * (1-t)^k) = 1 := by
  interval_cases k
  · let c : Fin 7 → ℝ := ![16, -120, 240, -140, 0, 0, 0]
    have ht (t : ℝ) : endpointKernel t * (1-t)^0 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]
  · let c : Fin 7 → ℝ := ![16, -136, 360, -380, 140, 0, 0]
    have ht (t : ℝ) : endpointKernel t * (1-t)^1 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]
  · let c : Fin 7 → ℝ := ![16, -152, 496, -740, 520, -140, 0]
    have ht (t : ℝ) : endpointKernel t * (1-t)^2 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]
  · let c : Fin 7 → ℝ := ![16, -168, 648, -1236, 1260, -660, 140]
    have ht (t : ℝ) : endpointKernel t * (1-t)^3 =
        ∑ j ∈ Finset.range 7, c ⟨j % 7, Nat.mod_lt _ (by norm_num)⟩ * t^j := by
      simp [c, endpointKernel, Finset.sum_range_succ]
      ring
    simp_rw [ht]
    rw [integral_polynomial_sum]
    norm_num [c, Finset.sum_range_succ]

end CriticalPercolation.FiniteEntropy

end
end

end OAI
