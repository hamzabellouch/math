import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDivisorRangesSelection

namespace OAI

namespace Ostmann.QuadraticSieve

theorem exists_uniform_divisor_range_scales (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ),
      0 < D → 0 < N → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      ∃ p ∈ divisorRangeScales D, ∀ a b : ℕ → ℂ,
        (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
          ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖)^2 ≤
          C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
            quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
            quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
            coefficientEnergy S a*coefficientEnergy T b := by
  obtain ⟨C,hC,hbound⟩ := product_divisor_dyadic_bound_all ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T hD hN hV hS hT
  have hne : (divisorRangeScales D).Nonempty := by
    refine ⟨(D,1),mem_divisorRangeScales.mpr ?_⟩
    simp only [mul_one]
    omega
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image (divisorRangeScales D)
    (fun p => (p.1*p.2 : ℕ)*quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
      quadraticNorm V (oddSquarefreeUpTo (N/p.2))) hne
  refine ⟨p,hp,?_⟩
  intro a b
  obtain ⟨L₁,L₂,h1,h2,hlo,hhi,hup1,hup2,h⟩ := hbound D N V S T a b hD hN hV hS hT
  have hm := hmax (L₁,L₂) (mem_divisorRangeScales.mpr ⟨h1,h2,hlo,hhi,hup1,hup2⟩)
  apply h.trans
  have he : 0 ≤ coefficientEnergy S a * coefficientEnergy T b :=
    mul_nonneg (coefficientEnergy_nonneg _ _) (coefficientEnergy_nonneg _ _)
  have hc : 0 ≤ C*(N : ℝ)^ε := by positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hc) he
  simpa only [mul_assoc] using hh

end Ostmann.QuadraticSieve

end OAI
