import OAI.MeasureTheory.Falconer.Estimates.EnergyOriginalKernel
import OAI.MeasureTheory.Falconer.Fourier.NoncomparableOriginalIntegral
import OAI.MeasureTheory.Falconer.Fourier.JetStateEnvelope

namespace OAI

/-! # The actual recursive angular state on its original four-point law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

theorem jetStateEnergy_original_kernel {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (m+3)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (M P a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (jetStateEnergy Q ρ profile N σ J i S A μ ν M P a v Ψ f g : ℂ) =
      ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹))) •
        ∫ z, jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z
          ∂(μ.prod μ).prod (ν.prod ν) := by
  have hB : 0 ≤ (descriptorJetBound (m+3) K)^K*A⁻¹ :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hA.le)
  have h := independentAngularEnergy_four_point μ ν M P a v Ψ
    (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A)
    (f.value_measurable Q ρ profile N σ J i S A)
    (g.value_measurable Q ρ profile N σ J i S A) hB hB
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

theorem jetStateEnergy_le_original_kernel {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (m+3)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    ENNReal.ofReal (jetStateEnergy Q ρ profile N σ J i S A μ ν M P a v Ψ f g) ≤
      ENNReal.ofReal ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹))) *
        ∫⁻ z, ENNReal.ofReal ‖jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z‖
          ∂(μ.prod μ).prod (ν.prod ν) := by
  have he := jetStateEnergy_original_kernel f g w₀ Q ρ profile N σ J i S hF hG hA μ ν M P a v Ψ
  have hnonneg : 0 ≤ jetStateEnergy Q ρ profile N σ J i S A μ ν M P a v Ψ f g :=
    independentAngularEnergy_nonneg _ _ _ _ _
  have hcoef : 0 ≤ (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹)) := by positivity
  have hnorm : jetStateEnergy Q ρ profile N σ J i S A μ ν M P a v Ψ f g =
      ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹))) *
        ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z
          ∂(μ.prod μ).prod (ν.prod ν)‖ := by
    calc
      _ = ‖(jetStateEnergy Q ρ profile N σ J i S A μ ν M P a v Ψ f g : ℂ)‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
      _ = _ := by rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoef]
  rw [hnorm, ENNReal.ofReal_mul hcoef]
  apply mul_le_mul' le_rfl
  simpa only [← ofReal_norm] using
    (enorm_integral_le_lintegral_enorm
      (μ := (μ.prod μ).prod (ν.prod ν))
      (jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ))

end Falconer

end OAI
