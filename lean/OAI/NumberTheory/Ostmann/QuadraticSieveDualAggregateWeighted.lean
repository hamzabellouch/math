import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNorm
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateScale
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderRows

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem norm_weighted_rectangle_le {ι κ : Type*} (D : Finset ι) (V : Finset κ)
    (w f : ι → κ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ d ∈ D, ∀ v ∈ V, ‖w d v‖ ≤ A) :
    ‖∑ d ∈ D, ∑ v ∈ V, w d v * f d v‖ ≤ A * ∑ d ∈ D, ∑ v ∈ V, ‖f d v‖ := by
  calc
    _ ≤ ∑ d ∈ D, ∑ v ∈ V, ‖w d v * f d v‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => norm_sum_le _ _))
    _ ≤ ∑ d ∈ D, ∑ v ∈ V, A * ‖f d v‖ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul]
      exact mul_le_mul (hw d hd v hv) le_rfl (norm_nonneg _) hA
    _ = _ := by simp_rw [←Finset.mul_sum]

theorem dual_gauss_weighted_range_bounds (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S : Finset ℕ) (H : ℝ),
      0 < D → 0 < N → 0 < H → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, H ≤ (n : ℝ)) →
      ∃ p ∈ divisorRangeScales D, ∀ (a : ℕ → ℂ) (c : ℤ) (w : ℕ → ℕ → ℂ) (A : ℝ),
        0 ≤ A → (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ V, ‖w d v‖ ≤ A) →
        (‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
          w d v * gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v : ℤ)‖ ≤
          A*(2/H)*Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
            quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
            coefficientEnergy S a*coefficientEnergy S a)) ∧
        (‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
          w d v * gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) c d (v : ℤ)‖ ≤
          A*(2*(N : ℝ)/H)*Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
            quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
            coefficientEnergy S a*coefficientEnergy S a)) := by
  obtain ⟨C,hC,hbound⟩ := gauss_product_divisor_range_bound ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S H hD hN hH hV hS hSH
  obtain ⟨p,hp,hrow⟩ := hbound D N V S S H hD hN hH hV hS hS hSH hSH
  refine ⟨p,hp,?_⟩
  intro a c w A hA hw
  have hQ1 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/p.1))
  have hQ2 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/p.2))
  have hE := coefficientEnergy_nonneg S a
  constructor
  · apply (norm_weighted_rectangle_le _ _ _ _ A hA hw).trans
    have hr := hrow a (fun n => conj (a n)) c
    rw [coefficientEnergy_conj] at hr
    exact (mul_le_mul_of_nonneg_left hr hA).trans_eq (by ring)
  · apply (norm_weighted_rectangle_le _ _ _ _ A hA hw).trans
    have hr := hrow (sqrtCoefficients a) (sqrtCoefficients (fun n => conj (a n))) c
    have hEa := coefficientEnergy_sqrtCoefficients_le S a N
      (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).2.1)
    have hEb := coefficientEnergy_sqrtCoefficients_le S (fun n => conj (a n)) N
      (fun n hn => (mem_oddSquarefreeUpTo.mp (hS hn)).2.1)
    rw [coefficientEnergy_conj] at hEb
    have hbase : 0 ≤ C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
        quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2)) := by positivity
    have hrad := Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul_of_nonneg_left hEa hbase) hEb
      (coefficientEnergy_nonneg _ _) (by positivity))
    rw [show C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
        quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
        ((N : ℝ)*coefficientEnergy S a)*((N : ℝ)*coefficientEnergy S a) =
        (N : ℝ)^2*(C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
          quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
          coefficientEnergy S a*coefficientEnergy S a) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg N)] at hrad
    have hh := (mul_le_mul_of_nonneg_left hr hA).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad
        (show 0 ≤ 2/H by positivity)) hA)
    convert hh using 1; ring

end Ostmann.QuadraticSieve

end OAI
