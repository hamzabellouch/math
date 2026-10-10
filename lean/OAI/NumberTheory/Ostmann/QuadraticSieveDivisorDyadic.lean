import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorDyadicCover
import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorDyadicGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorDyadicVanishing

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Finset

theorem product_divisor_dyadic_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ),
      0<D → 0<N → D≤N^2 → (∀ v∈V,Odd v) →
      S⊆oddSquarefreeUpTo N → T⊆oddSquarefreeUpTo N →
      ∃ L₁ L₂ : ℕ, 0<L₁ ∧ 0<L₂ ∧ D<4*(L₁*L₂) ∧ L₁*L₂≤2*D ∧
        L₁≤2*D ∧ L₂≤2*D ∧
        (∑ d∈Ioc D (2*D),∑ v∈V,‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖)^2 ≤
          C*(N : ℝ)^ε*(L₁*L₂ : ℕ)*
            quadraticNorm V (oddSquarefreeUpTo (N/L₁))*
            quadraticNorm V (oddSquarefreeUpTo (N/L₂))*coefficientEnergy S a*coefficientEnergy T b := by
  obtain ⟨C₁,hC₁,hrect⟩ := divisor_rectangle_bound (ε/2) (by positivity)
  obtain ⟨C₂,hC₂,hdepth⟩ := divisorDyadicDepth_fourth_le_rpow (ε/2) (by positivity)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro D N V S T a b hD hN hDN hV hS hT
  obtain ⟨k,hk,hsel⟩ := exists_divisor_dyadic_rectangle hD V S T a b
  obtain ⟨hL₁,hL₂,hprodlo,hprodhi,hup₁,hup₂⟩ := divisorDyadicIndices_scales hD hk
  refine ⟨2^k.1,2^k.2,hL₁,hL₂,hprodlo,hprodhi,hup₁,hup₂,?_⟩
  have hrect' := hrect (dyadicDivisors k.1) (dyadicDivisors k.2) V S T a b N
    (2^k.1) (2^k.2) hL₁ hL₂ (fun d hd => (mem_Ico.mp hd).1)
    (fun d hd => (mem_Ico.mp hd).1) hV hS hT
  simp only [dyadicDivisors_card] at hrect'
  have hsum0 : 0≤∑ d∈Ioc D (2*D),∑ v∈V,
      ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => norm_nonneg _))
  have hsel2 := pow_le_pow_left₀ hsum0 hsel 2
  rw [mul_pow,←pow_mul] at hsel2
  norm_num only at hsel2
  have hcost := hdepth D N hD hN hDN
  have hQa := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/2^k.1))
  have hQb := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/2^k.2))
  have hEa := coefficientEnergy_nonneg S a
  have hEb := coefficientEnergy_nonneg T b
  have hpow : ((N : ℝ)^(ε/2))^2=(N : ℝ)^ε := by
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    ring
  apply hsel2.trans
  calc
    _ ≤ (divisorDyadicDepth D : ℝ)^4 *
        (C₁*(N : ℝ)^(ε/2)*(2^k.1 : ℕ)*(2^k.2 : ℕ)*
          quadraticNorm V (oddSquarefreeUpTo (N/2^k.1))*
          quadraticNorm V (oddSquarefreeUpTo (N/2^k.2))*coefficientEnergy S a*coefficientEnergy T b) :=
      mul_le_mul_of_nonneg_left hrect' (by positivity)
    _ ≤ (C₂*(N : ℝ)^(ε/2))*
        (C₁*(N : ℝ)^(ε/2)*(2^k.1 : ℕ)*(2^k.2 : ℕ)*
          quadraticNorm V (oddSquarefreeUpTo (N/2^k.1))*
          quadraticNorm V (oddSquarefreeUpTo (N/2^k.2))*coefficientEnergy S a*coefficientEnergy T b) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = (C₁*C₂)*((N : ℝ)^(ε/2))^2*(2^k.1*2^k.2 : ℕ)*
          quadraticNorm V (oddSquarefreeUpTo (N/2^k.1))*
          quadraticNorm V (oddSquarefreeUpTo (N/2^k.2))*coefficientEnergy S a*coefficientEnergy T b := by
      push_cast
      ring
    _ = _ := by rw [hpow]

theorem product_divisor_dyadic_bound_all (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ),
      0<D → 0<N → (∀ v∈V,Odd v) →
      S⊆oddSquarefreeUpTo N → T⊆oddSquarefreeUpTo N →
      ∃ L₁ L₂ : ℕ, 0<L₁ ∧ 0<L₂ ∧ D<4*(L₁*L₂) ∧ L₁*L₂≤2*D ∧
        L₁≤2*D ∧ L₂≤2*D ∧
        (∑ d∈Ioc D (2*D),∑ v∈V,‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖)^2 ≤
          C*(N : ℝ)^ε*(L₁*L₂ : ℕ)*
            quadraticNorm V (oddSquarefreeUpTo (N/L₁))*
            quadraticNorm V (oddSquarefreeUpTo (N/L₂))*coefficientEnergy S a*coefficientEnergy T b := by
  obtain ⟨C,hC,hbound⟩ := product_divisor_dyadic_bound ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T a b hD hN hV hS hT
  by_cases hDN : D≤N^2
  · exact hbound D N V S T a b hD hN hDN hV hS hT
  · refine ⟨D,1,hD,by omega,by omega,by omega,by omega,by omega,?_⟩
    rw [product_divisor_annulus_eq_zero_of_large V S T a b (by omega) hS hT]
    simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_one,Nat.div_one]
    have hQa := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/D))
    have hQb := quadraticNorm_nonneg V (oddSquarefreeUpTo N)
    have hEa := coefficientEnergy_nonneg S a
    have hEb := coefficientEnergy_nonneg T b
    positivity

end Ostmann.QuadraticSieve

end

end OAI
