import OAI.MeasureTheory.Falconer.Radial.FarRadialIntegral
import OAI.MeasureTheory.Falconer.Fourier.JetStateFarExpansion
import OAI.MeasureTheory.Falconer.Shells.PositiveSuffix

namespace OAI

/-! # Comparable far kernels for the exact descriptor-jet states -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_far_radial_kernel (m K L J : ℕ) (hJL : 2*J ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B H : ℝ, 1 ≤ B ∧ 0 ≤ H ∧
      ∀ (F : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (x x' y y' : Space (m+3))
        (e e' : Sphere (m+3)),
      ∀ R d₁ d₂ : ℝ, 0 < R → 0 < d₁ → 0 < d₂ →
      (2*(E+Dq))^2 ≤ R*d₁ → (2*(E+Dq))^2 ≤ R*d₂ →
      ‖R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*
        stationarySphereApprox m J (r*d₁) (f.pairAmbient Q ρ profile N σ J₀ i S A x x') e*
        stationarySphereApprox m J (r*d₂) (g.pairAmbient Q ρ profile N σ J₀ i S A y y') e')‖ ≤
      H*(B^K*A⁻¹)^4*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  obtain ⟨B,hB,hbudget⟩ := exists_descriptorJetSymbol_pair_budget (m+1) K L
  obtain ⟨C,hC,hkernel⟩ := full_stationary_radial_bound hΨ hs m J
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f g x x' y y' e e' R d₁ d₂ hR hd₁ hd₂ hscale₁ hscale₂
  have hf (t : ℕ) (ht : t ≤ 2*J) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hscale hE f x x' t
      (ht.trans hJL) w
  have hg (t : ℕ) (ht : t ≤ 2*J) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hscale hE g y y' t
      (ht.trans hJL) w
  have h := hkernel _ _ (f.pairAmbient_smooth Q ρ profile N σ J₀ i S A x x')
    (g.pairAmbient_smooth Q ρ profile N σ J₀ i S A y y') _ _ _ R d₁ d₂
    (sq_nonneg _) (sq_nonneg _) hD hR hd₁ hd₂ hscale₁ hscale₂ hf hg e e'
  apply h.trans_eq
  ring

theorem signedRadialCoefficient_state_support {m K L : ℕ}
    {F G H : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (hHF : H ⊆ F) (hHG : H ⊆ G)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x x' y y' : Space (m+3)) (Ψ : ℝ → ℝ) (j k : ℕ)
    (R d₁ d₂ s : ℝ) (ε η : Bool)
    (hne : signedRadialCoefficient m j k Ψ
      (f.pairAmbient Q ρ profile N σ J i S A x x')
      (g.pairAmbient Q ρ profile N σ J i S A y y')
      (normalizeToSphere w₀ (x-x')) (normalizeToSphere w₀ (y-y')) R d₁ d₂ ε η s ≠ 0) :
    (x,x') ∈ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H ∧
      (y,y') ∈ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H := by
  have hf : signedStationaryCoefficient m j (R*d₁)
      (f.pairAmbient Q ρ profile N σ J i S A x x') (normalizeToSphere w₀ (x-x')) ε ≠ 0 := by
    intro hz
    exact hne (by simp only [signedRadialCoefficient,hz,zero_mul,mul_zero])
  have hg : signedStationaryCoefficient m k (R*d₂)
      (g.pairAmbient Q ρ profile N σ J i S A y y') (normalizeToSphere w₀ (y-y')) η ≠ 0 := by
    intro hz
    exact hne (by simp only [signedRadialCoefficient,hz,mul_zero,zero_mul])
  have hleft := f.signed_stationary_support Q ρ profile N σ J i S A x x'
    (normalizeToSphere w₀ (x-x')) j (R*d₁) ε hf
  have hright := g.signed_stationary_support Q ρ profile N σ J i S A y y'
    (normalizeToSphere w₀ (y-y')) k (R*d₂) η hg
  exact ⟨fun b hb => hleft b (hHF hb),fun b hb => hright b (hHG hb)⟩

end Falconer

end OAI
