import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateScale
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateWeighted
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBoundary
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderRows

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem dual_gauss_weighted_boundary_bounds (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (V S : Finset ℕ) (H : ℝ),
      0 < N → 0 < H → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, H ≤ (n : ℝ)) →
      ∀ (a : ℕ → ℂ) (c : ℤ) (w : ℕ → ℂ) (A : ℝ),
        0 ≤ A → (∀ v ∈ V, ‖w v‖ ≤ A) →
        (‖∑ v ∈ V,
          w v * gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c 1 (v : ℤ)‖ ≤
          A*(2/H)*Real.sqrt (C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
            coefficientEnergy S a*coefficientEnergy S a)) ∧
        (‖∑ v ∈ V,
          w v * gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) c 1 (v : ℤ)‖ ≤
          A*(2*(N : ℝ)/H)*Real.sqrt (C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
            coefficientEnergy S a*coefficientEnergy S a)) := by
  obtain ⟨C,hC,hbound⟩ := gauss_product_boundary_bound ε hε
  refine ⟨C,hC,?_⟩
  intro N V S H hN hH hV hS hSH a c w A hA hw
  have hQ := quadraticNorm_nonneg V (oddSquarefreeUpTo N)
  have hE := coefficientEnergy_nonneg S a
  have hweighted (f : ℕ → ℂ) : ‖∑ v ∈ V, w v*f v‖ ≤ A*∑ v ∈ V, ‖f v‖ := by
    calc
      _ ≤ ∑ v ∈ V, ‖w v*f v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ V, A*‖f v‖ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hw v hv) (norm_nonneg _)
      _ = _ := (Finset.mul_sum ..).symm
  constructor
  · apply (hweighted _).trans
    have hr := hbound N V S S H hN hH hV hS hS hSH hSH a (fun n => conj (a n)) c
    rw [coefficientEnergy_conj] at hr
    exact (mul_le_mul_of_nonneg_left hr hA).trans_eq (by ring)
  · apply (hweighted _).trans
    have hr := hbound N V S S H hN hH hV hS hS hSH hSH
      (sqrtCoefficients a) (sqrtCoefficients (fun n => conj (a n))) c
    have hEa := coefficientEnergy_sqrtCoefficients_le S a N
      (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).2.1)
    have hEb := coefficientEnergy_sqrtCoefficients_le S (fun n => conj (a n)) N
      (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).2.1)
    rw [coefficientEnergy_conj] at hEb
    have hbase : 0 ≤ C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2 := by positivity
    have hrad := Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul_of_nonneg_left hEa hbase) hEb
      (coefficientEnergy_nonneg _ _) (by positivity))
    rw [show C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
        ((N : ℝ)*coefficientEnergy S a)*((N : ℝ)*coefficientEnergy S a) =
        (N : ℝ)^2*(C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
          coefficientEnergy S a*coefficientEnergy S a) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg N)] at hrad
    have hh := (mul_le_mul_of_nonneg_left hr hA).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad
        (show 0 ≤ 2/H by positivity)) hA)
    convert hh using 1; ring

end Ostmann.QuadraticSieve

end OAI
