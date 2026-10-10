import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDivisorRangesSelection

namespace OAI

namespace Ostmann.QuadraticSieve

theorem product_divisor_weighted_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ),
      0 < D → 0 < N → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      ∃ p ∈ divisorRangeScales D, ∀ (w : ℕ → ℕ → ℂ) (H : ℝ),
        0 ≤ H → (∀ d ∈ Finset.Ioc D (2 * D), ∀ v ∈ V, ‖w d v‖ ≤ H) →
        ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
          w d v * coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ ≤
          H * Real.sqrt (C * (N : ℝ) ^ ε * (p.1 * p.2 : ℕ) *
            quadraticNorm V (oddSquarefreeUpTo (N / p.1)) *
            quadraticNorm V (oddSquarefreeUpTo (N / p.2)) *
            coefficientEnergy S a * coefficientEnergy T b) := by
  obtain ⟨C,hC,hbound⟩ := product_divisor_dyadic_bound_all ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T a b hD hN hV hS hT
  obtain ⟨L₁,L₂,h1,h2,hlo,hhi,hup1,hup2,hrange⟩ := hbound D N V S T a b hD hN hV hS hT
  refine ⟨(L₁,L₂),mem_divisorRangeScales.mpr ⟨h1,h2,hlo,hhi,hup1,hup2⟩,?_⟩
  intro w H hH hw
  let E := C * (N : ℝ) ^ ε * (L₁ * L₂ : ℕ) *
    quadraticNorm V (oddSquarefreeUpTo (N / L₁)) *
    quadraticNorm V (oddSquarefreeUpTo (N / L₂)) * coefficientEnergy S a * coefficientEnergy T b
  have hQ1 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N / L₁))
  have hQ2 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N / L₂))
  have hEa := coefficientEnergy_nonneg S a
  have hEb := coefficientEnergy_nonneg T b
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hsum : 0 ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hs : (∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ≤ Real.sqrt E := by
    change _ ≤ E at hrange
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
        ‖w d v * coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
        H * ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hw d hd v hv) (norm_nonneg _)
    _ = H * ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
        ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ := by simp_rw [← Finset.mul_sum]
    _ ≤ H * Real.sqrt E := mul_le_mul_of_nonneg_left hs hH
    _ = _ := rfl

end Ostmann.QuadraticSieve

end OAI
