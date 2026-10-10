import OAI.NumberTheory.Ostmann.QuadraticSieveComplementRecursionScale
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementWeightedRanges

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem complementary_range_bootstrap_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ)
      (M B x H Δ A : ℝ) (r : ℕ) (g : ℕ → ℕ → ℂ),
      0 < D → 0 < N → 0 < M → 0 < B → 0 ≤ x → 0 ≤ H → 1 ≤ Δ → 0 ≤ A → 0 < r →
      (∀ v ∈ V, Odd v ∧ B ≤ (v : ℝ)) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (Real.sqrt (M/B)/Δ ≤ (D : ℝ)/4) →
      (∀ j : ℕ, 0 < j → quadraticNorm V (oddSquarefreeUpTo (N/j)) ≤ H*(x+(N : ℝ)/j)) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ V, ‖g d v‖ ≤ A) →
      ‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
        (μ r : ℂ)*(μ d : ℂ)*((Real.sqrt (M/v)/((r : ℝ)*d) : ℝ) : ℂ)*g d v*
          coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ ≤
        (2*A*H/(r : ℝ))*Real.sqrt (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy T b)*
          (Real.sqrt (M/B)*x+Δ*N) := by
  obtain ⟨C,hC,hbound⟩ := complementary_weighted_divisor_range_bound ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T a b M B x H Δ A r g hD hN hM hB hx hH hΔ hA hr hV hS hT htrans hnorm hg
  obtain ⟨p,hp,hrow⟩ := hbound D N V S T a b M B hD hN hM hB hV hS hT
  obtain ⟨hp1,hp2,hplo,hphi,hpup1,hpup2⟩ := mem_divisorRangeScales.mp hp
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hDp : 0 < (D : ℝ) := by exact_mod_cast hD
  have hp1r : 1 ≤ (p.1 : ℝ) := by exact_mod_cast hp1
  have hp2r : 1 ≤ (p.2 : ℝ) := by exact_mod_cast hp2
  have hpp : (p.1 : ℝ)*p.2 ≤ 2*D := by exact_mod_cast hphi
  have hlow : (D : ℝ) < 4*((p.1 : ℝ)*p.2) := by exact_mod_cast hplo
  have htransition : Real.sqrt (M/B)/Δ ≤ (p.1 : ℝ)*p.2 := by linarith
  have hQ1 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/p.1))
  have hQ2 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/p.2))
  have hscalar := complement_range_bootstrap_scale hM hNp hB hx hH hDp hp1r hp2r hΔ
    hpp htransition hQ1 hQ2 (hnorm p.1 hp1) (hnorm p.2 hp2)
  have hEa := coefficientEnergy_nonneg S a
  have hEb := coefficientEnergy_nonneg T b
  have hbase : 0 ≤ C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy T b := by positivity
  apply (hrow r hr g A hA hg).trans
  have hrad : C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
      quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
      coefficientEnergy S a*coefficientEnergy T b =
      (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy T b)*
        (((p.1 : ℝ)*p.2)*quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
          quadraticNorm V (oddSquarefreeUpTo (N/p.2))) := by push_cast; ring
  rw [hrad,Real.sqrt_mul hbase]
  have h := mul_le_mul_of_nonneg_left hscalar
    (show 0 ≤ (A/(r : ℝ))*Real.sqrt (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy T b) by positivity)
  convert h using 1 <;> ring

end Ostmann.QuadraticSieve

end OAI
