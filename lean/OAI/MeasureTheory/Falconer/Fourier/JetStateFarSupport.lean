import OAI.MeasureTheory.Falconer.Fourier.JetStateFarKernel

namespace OAI

/-! # All original descriptor tests survive the full far radial sum -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

theorem stationarySphereApprox_eq_zero_of_not_tested {m K L : ℕ}
    {F H : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (hHF : H ⊆ F)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (A : ℝ) (x y : Space (m+3))
    (hbad : (x,y) ∉ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H)
    (M : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    stationarySphereApprox m M Λ (f.pairAmbient Q ρ profile N σ J i S A x y)
      (normalizeToSphere w₀ (x-y)) = 0 := by
  have hc (j : ℕ) (ε : Bool) : signedStationaryCoefficient m j Λ
      (f.pairAmbient Q ρ profile N σ J i S A x y) (normalizeToSphere w₀ (x-y)) ε = 0 := by
    by_contra hn
    apply hbad
    intro b hb
    exact f.signed_stationary_support Q ρ profile N σ J i S A x y
      (normalizeToSphere w₀ (x-y)) j Λ ε hn b (hHF hb)
  rw [stationarySphereApprox_pole_sum m M hΛ]
  simp only [stationaryPoleTerm, hc, mul_zero, Finset.sum_const_zero]

end DescriptorJetSymbol

noncomputable def jetStateStationaryKernel {m K L : ℕ}
    {F : Finset PolicyDescriptor} {Dq : ℝ}
    (f g : DescriptorJetSymbol (m+1) K L F Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (A : ℝ)
    (M : ℕ) (R : ℝ) (Ψ : ℝ → ℝ)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) : ℂ :=
  R⁻¹ • ∫ r : ℝ, (Ψ (r/R):ℂ)*
    stationarySphereApprox m M (r*dist z.1.1 z.1.2)
      (f.pairAmbient Q ρ profile N σ J i S A z.1.1 z.1.2)
      (normalizeToSphere w₀ (z.1.1-z.1.2))*
    stationarySphereApprox m M (r*dist z.2.1 z.2.2)
      (g.pairAmbient Q ρ profile N σ J i S A z.2.1 z.2.2)
      (normalizeToSphere w₀ (z.2.1-z.2.2))

theorem jetStateStationaryKernel_eq_zero_of_not_tested {m K L : ℕ}
    {F H : Finset PolicyDescriptor} {Dq : ℝ}
    (f g : DescriptorJetSymbol (m+1) K L F Dq) (hHF : H ⊆ F)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (A : ℝ)
    (M : ℕ) {R : ℝ} (hR : 0 < R) (Ψ : ℝ → ℝ)
    (hΨ : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))
    (hd₁ : 0 < dist z.1.1 z.1.2) (hd₂ : 0 < dist z.2.1 z.2.2)
    (hbad : z ∉ (descriptorPairTests w₀ Q ρ profile N σ J (i+1) H) ×ˢ
      (descriptorPairTests w₀ Q ρ profile N σ J (i+1) H)) :
    jetStateStationaryKernel f g w₀ Q ρ profile N σ J i S A M R Ψ z = 0 := by
  have hz (r : ℝ) : (Ψ (r/R):ℂ)*
      stationarySphereApprox m M (r*dist z.1.1 z.1.2)
        (f.pairAmbient Q ρ profile N σ J i S A z.1.1 z.1.2)
        (normalizeToSphere w₀ (z.1.1-z.1.2))*
      stationarySphereApprox m M (r*dist z.2.1 z.2.2)
        (g.pairAmbient Q ρ profile N σ J i S A z.2.1 z.2.2)
        (normalizeToSphere w₀ (z.2.1-z.2.2)) = 0 := by
    by_cases hp : Ψ (r/R) = 0
    · simp only [hp, Complex.ofReal_zero, zero_mul]
    have hr : 0 < r := by
      have hh := (lt_div_iff₀ hR).mp (hΨ _ hp).1
      nlinarith
    by_cases hleft : z.1 ∈ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H
    · have hright : z.2 ∉ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H :=
        fun h => hbad ⟨hleft,h⟩
      rw [g.stationarySphereApprox_eq_zero_of_not_tested hHF w₀ Q ρ profile N σ J i S A
        z.2.1 z.2.2 hright M (mul_pos hr hd₂), mul_zero]
    · rw [f.stationarySphereApprox_eq_zero_of_not_tested hHF w₀ Q ρ profile N σ J i S A
        z.1.1 z.1.2 hleft M (mul_pos hr hd₁), mul_zero, zero_mul]
  unfold jetStateStationaryKernel
  simp only [hz, integral_zero, smul_zero]

end Falconer

end OAI
