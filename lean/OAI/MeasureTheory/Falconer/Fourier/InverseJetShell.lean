import OAI.MeasureTheory.Falconer.Fourier.InverseJetCoefficient
import OAI.MeasureTheory.Falconer.Fourier.InverseJetIntegration
import OAI.MeasureTheory.Falconer.Fourier.JetStateBudgetOrder

namespace OAI

/-! # A common recursive budget for the complete finite inverse

Both descriptor lists and original endpoint laws stay fixed. The frequency
coefficient absorbs the added jet orders before the finite sum is bounded.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

abbrev DescriptorInverseFamilyIndex {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F D)
    (g : DescriptorJetSymbol (m+1) K L G D) (k : ℕ) :=
  (j : Fin (k+1)) × DescriptorInverseIndex f g j.val

noncomputable def descriptorInverseShellCost {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F D)
    (g : DescriptorJetSymbol (m+1) K L G D)
    (k : ℕ) (A B : Fin (k+1) → ℝ) (Af Ag U δ W : ℝ)
    (hδ : 0 < δ) (hW : 0 < W) : ℝ :=
  (Fintype.card (DescriptorInverseFamilyIndex f g k) : ℝ)*
    ∑ z : DescriptorInverseFamilyIndex f g k,
      ((|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))^2*
        (spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2

noncomputable def descriptorInverseNormalizedSum {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) (M P a v r : ℝ) : ℂ :=
  ∑ z : DescriptorInverseFamilyIndex f g k,
    ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
      (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
      ((T z.1).coefficient N σ Af Ag U U z.2 : ℂ)*
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW z.1.val)
          (spatialEndpointFamily μ M s (((T z.1).left z.2).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star (((T z.1).right z.2).value Q ρ profile N σ J i S U x w))) r

theorem descriptor_inverse_family_shell_integrable {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    Integrable (fun r => ‖descriptorInverseNormalizedSum k R A B T Q ρ profile N σ J i S
      Af Ag U δ W hδ hW s μ ν M P a v r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  unfold descriptorInverseNormalizedSum
  let C₀ (z : DescriptorInverseFamilyIndex f g k) :=
    (descriptorJetBound (m+3) (K+2*z.1.val))^(K+2*z.1.val)*U⁻¹
  have hC₀ (z : DescriptorInverseFamilyIndex f g k) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_sum_integrable (ι := DescriptorInverseFamilyIndex f g k) Finset.univ a v Ψ δ W hδ hW (fun (z : DescriptorInverseFamilyIndex f g k) => z.1.val)
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily μ M s (((T z.1).left z.2).value Q ρ profile N σ J i S U))
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily ν P s
      (fun x w => star (((T z.1).right z.2).value Q ρ profile N σ J i S U x w)))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable μ M s _
      (((T z.1).left z.2).value_measurable Q ρ profile N σ J i S U))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((T z.1).right z.2).value_measurable Q ρ profile N σ J i S U)))
    (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*μ.real univ/M) (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*ν.real univ/P)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le μ hM s _
      (((T z.1).left z.2).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((T z.1).right z.2).value_norm_le Q ρ profile N σ J i S hG hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((T z.1).coefficient N σ Af Ag U U z.2 : ℂ))
    (fun z => (|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))
  · intro z _
    fun_prop
  · intro z _
    positivity
  · filter_upwards [hregime] with r hr
    intro z _
    have hp : ((2:ℝ)^(v-a))^(((m+2:ℕ):ℝ)/2) =
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) :=
      (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    rw [← hp]
    exact (T z.1).normalized_coefficient_le (h := (((m+2:ℕ):ℝ)/2)) hD N σ Af Ag U hE hDE hFE hGE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2

theorem descriptor_inverse_family_shell_le {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖descriptorInverseNormalizedSum k R A B T Q ρ profile N σ J i S
        Af Ag U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (Fintype.card (DescriptorInverseFamilyIndex f g k) : ℝ)*
        ∑ z : DescriptorInverseFamilyIndex f g k,
          ((|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))^2*
            ((spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2*
              jetStateEnvelope (m+1) (K+2*k) R D F G Q ρ profile N σ J i S U μ ν M P a v Ψ) := by
  unfold descriptorInverseNormalizedSum
  let C₀ (z : DescriptorInverseFamilyIndex f g k) :=
    (descriptorJetBound (m+3) (K+2*z.1.val))^(K+2*z.1.val)*U⁻¹
  have hC₀ (z : DescriptorInverseFamilyIndex f g k) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_le (ι := DescriptorInverseFamilyIndex f g k) Finset.univ a v Ψ δ W hδ hW (fun (z : DescriptorInverseFamilyIndex f g k) => z.1.val)
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily μ M s (((T z.1).left z.2).value Q ρ profile N σ J i S U))
    (fun (z : DescriptorInverseFamilyIndex f g k) => spatialEndpointFamily ν P s
      (fun x w => star (((T z.1).right z.2).value Q ρ profile N σ J i S U x w)))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable μ M s _
      (((T z.1).left z.2).value_measurable Q ρ profile N σ J i S U))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((T z.1).right z.2).value_measurable Q ρ profile N σ J i S U)))
    (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*μ.real univ/M) (fun (z : DescriptorInverseFamilyIndex f g k) => C₀ z*ν.real univ/P)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le μ hM s _
      (((T z.1).left z.2).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun (z : DescriptorInverseFamilyIndex f g k) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((T z.1).right z.2).value_norm_le Q ρ profile N σ J i S hG hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((T z.1).coefficient N σ Af Ag U U z.2 : ℂ))
    (fun z => (|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))
    (fun _ => jetStateEnvelope (m+1) (K+2*k) R D F G Q ρ profile N σ J i S U μ ν M P a v Ψ)
  · intro z _
    fun_prop
  · intro z _
    positivity
  · filter_upwards [hregime] with r hr
    intro z _
    have hp : ((2:ℝ)^(v-a))^(((m+2:ℕ):ℝ)/2) =
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) :=
      (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    rw [← hp]
    exact (T z.1).normalized_coefficient_le (h := (((m+2:ℕ):ℝ)/2)) hD N σ Af Ag U hE hDE hFE hGE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2
  · intro z _ ξ
    have hK : K+2*z.1.val ≤ K+2*k := by have := z.1.isLt; omega
    exact (spatial_endpoint_energy_le_jetStateEnvelope Q ρ profile N σ J i S hF hG hU
      μ ν hM hP s a v Ψ ((T z.1).left z.2) ((T z.1).right z.2) ξ).trans
      (jetStateEnvelope_budget_mono hK le_rfl hD.le le_rfl Q ρ profile N σ J i S
        hF hG hU μ ν hM hP a v Ψ)

end Falconer

end OAI
