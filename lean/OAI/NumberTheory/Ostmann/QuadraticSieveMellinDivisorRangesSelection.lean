import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorDyadic
import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationSelection

namespace OAI

namespace Ostmann.QuadraticSieve

def divisorRangeScales (D : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (2 * D)) ×ˢ (Finset.Icc 1 (2 * D))).filter
    (fun p => D < 4 * (p.1 * p.2) ∧ p.1 * p.2 ≤ 2 * D)

@[simp] theorem mem_divisorRangeScales {D : ℕ} {p : ℕ × ℕ} :
    p ∈ divisorRangeScales D ↔
      0 < p.1 ∧ 0 < p.2 ∧ D < 4 * (p.1 * p.2) ∧ p.1 * p.2 ≤ 2 * D ∧
        p.1 ≤ 2 * D ∧ p.2 ≤ 2 * D := by
  simp only [divisorRangeScales, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

theorem exists_uniform_mellin_divisor_scales (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ)
      (β γ : ℕ → ℝ) (σ : ℝ),
      0 < D → 0 < N → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, 0 < β n) → (∀ t ∈ T, 0 < γ t) →
      ∃ p ∈ divisorRangeScales D, ∀ r : ℝ,
        (∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) ^ 2 ≤
          C * (N : ℝ) ^ ε * (p.1 * p.2 : ℕ) *
            quadraticNorm V (oddSquarefreeUpTo (N / p.1)) *
            quadraticNorm V (oddSquarefreeUpTo (N / p.2)) *
            mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ := by
  obtain ⟨C,hC,hsep⟩ := product_divisor_dyadic_bound_all ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T a b β γ σ hD hN hV hS hT hβ hγ
  have hne : (divisorRangeScales D).Nonempty := by
    refine ⟨(D,1), mem_divisorRangeScales.mpr ?_⟩
    simp only [mul_one]
    omega
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image (divisorRangeScales D)
    (fun p => (p.1 * p.2 : ℕ) * quadraticNorm V (oddSquarefreeUpTo (N / p.1)) *
      quadraticNorm V (oddSquarefreeUpTo (N / p.2))) hne
  refine ⟨p,hp,?_⟩
  intro r
  obtain ⟨L₁,L₂,h1,h2,hlo,hhi,hup1,hup2,hbound⟩ :=
    hsep D N V S T (mellinTwist σ r β a) (mellinTwist σ r γ b) hD hN hV hS hT
  rw [coefficientEnergy_mellinTwist S a β σ r hβ,
    coefficientEnergy_mellinTwist T b γ σ r hγ] at hbound
  have hprod := hmax (L₁,L₂) (mem_divisorRangeScales.mpr ⟨h1,h2,hlo,hhi,hup1,hup2⟩)
  apply hbound.trans
  change C * (N : ℝ) ^ ε * (L₁ * L₂ : ℕ) *
      quadraticNorm V (oddSquarefreeUpTo (N / L₁)) * quadraticNorm V (oddSquarefreeUpTo (N / L₂)) *
      mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ ≤ _
  have hc : 0 ≤ C * (N : ℝ) ^ ε := by positivity
  have he : 0 ≤ mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ :=
    mul_nonneg (mellinWeightedEnergy_nonneg _ _ _ _) (mellinWeightedEnergy_nonneg _ _ _ _)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hc) he
  simpa only [mul_assoc] using h

end Ostmann.QuadraticSieve

end OAI
