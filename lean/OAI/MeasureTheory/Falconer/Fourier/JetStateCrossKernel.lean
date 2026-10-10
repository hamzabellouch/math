import OAI.MeasureTheory.Falconer.Fourier.JetStateOriginalEnergy
import OAI.MeasureTheory.Falconer.Angular.DyadicCapTerms
import OAI.MeasureTheory.Falconer.Estimates.CrossOriginalKernel

namespace OAI

/-! # Original four-point kernel for a single dyadic cross term -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem jetState_cross_original_kernel {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A)
    (μ μ' ν ν' : Measure (Space (m+3)))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (∫ z, (endpointTransform μ M (f.value Q ρ profile N σ J i S A) z.1 z.2.1 *
          endpointTransform ν P (g.value Q ρ profile N σ J i S A) z.1 z.2.2) *
        star (endpointTransform μ' M (f.value Q ρ profile N σ J i S A) z.1 z.2.1 *
          endpointTransform ν' P (g.value Q ρ profile N σ J i S A) z.1 z.2.2)
      ∂angularProductMeasure (m+3) v Ψ) =
      ((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹)) •
        ∫ z, jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z
          ∂(μ.prod μ').prod (ν.prod ν') := by
  have hB : 0 ≤ (descriptorJetBound (m+3) K)^K*A⁻¹ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hA.le)
  have h := endpoint_cross_original_kernel μ μ' ν ν' hM hP v Ψ
    (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A)
    (f.value_measurable Q ρ profile N σ J i S A)
    (g.value_measurable Q ρ profile N σ J i S A) hB
    (f.value_norm_le Q ρ profile N σ J i S hF hA)
    (g.value_norm_le Q ρ profile N σ J i S hG hA)
  apply h.trans
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  unfold jetStateOriginalKernel
  apply integral_congr_ae
  filter_upwards with r
  rw [vectorSphereIntegral_eq_oscillation w₀,vectorSphereIntegral_eq_oscillation w₀,
    dist_eq_norm,dist_eq_norm]

theorem dyadic_jetState_original_kernel {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (P₁ P₂ : DyadicCube (m+3))
    {M : ℝ} (hM : 0 < M) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (row col : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool)) :
    (∫ z, dyadicPairTransform P₁ P₂ ρ ρ M M
        (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A) row z *
      star (dyadicPairTransform P₁ P₂ ρ ρ M M
        (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A) col z)
      ∂angularProductMeasure (m+3) v Ψ) =
      ((M⁻¹*M⁻¹)*(M⁻¹*M⁻¹)) •
        ∫ z, jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z
          ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2) :=
  jetState_cross_original_kernel f g w₀ Q ρ profile N σ J i S hF hG hA
    _ _ _ _ hM hM v Ψ

end Falconer

end OAI
