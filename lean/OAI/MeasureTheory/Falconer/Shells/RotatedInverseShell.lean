import OAI.MeasureTheory.Falconer.Estimates.RotatedInverseCoefficient
import OAI.MeasureTheory.Falconer.Fourier.RotatedInverseIntegration
import OAI.MeasureTheory.Falconer.Fourier.InverseJetShell

namespace OAI

/-! # The full rotated inverse bounded by the original descriptor state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

abbrev RootInverseFamilyIndex (m k : ℕ) (F : Finset PolicyDescriptor) :=
  (j : Fin (k+1)) × RootInverseIndex m j.val F

noncomputable def rotatedInverseShellCost (m k : ℕ) (F : Finset PolicyDescriptor)
    (A : Fin (k+1) → ℝ) (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) : ℝ :=
  (Fintype.card (RootInverseFamilyIndex m k F) : ℝ)*
    ∑ z : RootInverseFamilyIndex m k F,
      ((|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))^2*
        (spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2

noncomputable def rotatedInverseNormalizedSum {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) (M P a v r : ℝ) : ℂ :=
  ∑ z : RootInverseFamilyIndex m k F,
    ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
      (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
      ((rootInverseWeight m z.1.val F N σ z.2*(U*A z.1)*U : ℝ) : ℂ)*
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW z.1.val)
          (spatialEndpointFamily μ M s (((H z.1).left z.2).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star (((H z.1).right z.2).value Q ρ profile N σ J i S U x w))) r


theorem rotated_inverse_family_shell_integrable {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    Integrable (fun r => ‖rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
      U δ W hδ hW s μ ν M P a v r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  unfold rotatedInverseNormalizedSum
  let C₀ (z : RootInverseFamilyIndex m k F) :=
    (descriptorJetBound (m+3) (2*z.1.val))^(2*z.1.val)*U⁻¹
  have hC₀ (z : RootInverseFamilyIndex m k F) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_sum_integrable (ι := RootInverseFamilyIndex m k F) Finset.univ a v Ψ δ W hδ hW (fun (z : RootInverseFamilyIndex m k F) => z.1.val)
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily μ M s (((H z.1).left z.2).value Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily ν P s
      (fun x w => star (((H z.1).right z.2).value Q ρ profile N σ J i S U x w)))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable μ M s _
      (((H z.1).left z.2).value_measurable Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((H z.1).right z.2).value_measurable Q ρ profile N σ J i S U)))
    (fun (z : RootInverseFamilyIndex m k F) => C₀ z*μ.real univ/M) (fun (z : RootInverseFamilyIndex m k F) => C₀ z*ν.real univ/P)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le μ hM s _
      (((H z.1).left z.2).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((H z.1).right z.2).value_norm_le Q ρ profile N σ J i S hF hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((rootInverseWeight m z.1.val F N σ z.2*(U*A z.1)*U : ℝ) : ℂ))
    (fun z => (|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))
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
    exact rotated_root_normalized_coefficient_le m z.1.val F N σ U (A z.1) hE hFE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2


theorem rotated_inverse_family_shell_le {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) :
    (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
        U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (Fintype.card (RootInverseFamilyIndex m k F) : ℝ)*
        ∑ z : RootInverseFamilyIndex m k F,
          ((|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))^2*
            ((spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2*
              jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ) := by
  unfold rotatedInverseNormalizedSum
  let C₀ (z : RootInverseFamilyIndex m k F) :=
    (descriptorJetBound (m+3) (2*z.1.val))^(2*z.1.val)*U⁻¹
  have hC₀ (z : RootInverseFamilyIndex m k F) : 0 ≤ C₀ z :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_le (ι := RootInverseFamilyIndex m k F) Finset.univ a v Ψ δ W hδ hW (fun (z : RootInverseFamilyIndex m k F) => z.1.val)
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily μ M s (((H z.1).left z.2).value Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) => spatialEndpointFamily ν P s
      (fun x w => star (((H z.1).right z.2).value Q ρ profile N σ J i S U x w)))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable μ M s _
      (((H z.1).left z.2).value_measurable Q ρ profile N σ J i S U))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp
        (((H z.1).right z.2).value_measurable Q ρ profile N σ J i S U)))
    (fun (z : RootInverseFamilyIndex m k F) => C₀ z*μ.real univ/M) (fun (z : RootInverseFamilyIndex m k F) => C₀ z*ν.real univ/P)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hM.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => div_nonneg (mul_nonneg (hC₀ z) measureReal_nonneg) hP.le)
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le μ hM s _
      (((H z.1).left z.2).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun (z : RootInverseFamilyIndex m k F) _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        (((H z.1).right z.2).value_norm_le Q ρ profile N σ J i S hF hU x w)))
    (fun z r =>
      ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
        (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        ((rootInverseWeight m z.1.val F N σ z.2*(U*A z.1)*U : ℝ) : ℂ))
    (fun z => (|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))
    (fun _ => jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ)
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
    exact rotated_root_normalized_coefficient_le m z.1.val F N σ U (A z.1) hE hFE
      hr.1 (by positivity) (by positivity) hr.2.1 hr.2.2 z.2
  · intro z _ ξ
    have hK : 2*z.1.val ≤ 2*k := by have := z.1.isLt; omega
    exact (spatial_endpoint_energy_le_jetStateEnvelope Q ρ profile N σ J i S hF hF hU
      μ ν hM hP s a v Ψ ((H z.1).left z.2) ((H z.1).right z.2) ξ).trans
      (jetStateEnvelope_budget_mono hK le_rfl (by norm_num) le_rfl Q ρ profile N σ J i S
        hF hF hU μ ν hM hP a v Ψ)

end Falconer

end OAI
