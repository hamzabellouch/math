import OAI.MeasureTheory.Falconer.Fourier.InverseClassIntegration
import OAI.MeasureTheory.Falconer.Fourier.JetStateSpatialShell

namespace OAI

/-! # Finite inverse factors bounded by the next actual state

The finite coefficients are separated from the original endpoint
transforms. Every energy on the right belongs to the exact descriptor
class constructed by the inverse, with its remaining derivative budget.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

theorem finite_shell_le (T : DescriptorInverseSymbols f g j R A B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U) (μ ν : Measure (Space (m+3)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (s a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (c : DescriptorInverseIndex f g j → ℝ → ℂ) (C : DescriptorInverseIndex f g j → ℝ)
    (hc : ∀ t, Measurable (c t)) (hC : ∀ t, 0 ≤ C t)
    (hcC : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ, ∀ t, ‖c t r‖ ≤ C t) :
    (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖∑ t : DescriptorInverseIndex f g j, c t r *
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
          (spatialEndpointFamily μ M s ((T.left t).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star ((T.right t).value Q ρ profile N σ J i S U x w))) r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (Fintype.card (DescriptorInverseIndex f g j) : ℝ)*
        ∑ t : DescriptorInverseIndex f g j, (C t)^2*
          ((spatialFourierCost (d := m+3) δ W hδ hW j)^2*
            jetStateEnvelope (m+1) (K+2*j) R D F G Q ρ profile N σ J i S U μ ν M P a v Ψ) := by
  let C₀ := (descriptorJetBound (m+3) (K+2*j))^(K+2*j)*U⁻¹
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  apply finite_spatial_shell_le Finset.univ a v Ψ δ W hδ hW (fun _ => j)
    (fun t => spatialEndpointFamily μ M s ((T.left t).value Q ρ profile N σ J i S U))
    (fun t => spatialEndpointFamily ν P s
      (fun x w => star ((T.right t).value Q ρ profile N σ J i S U x w)))
    (fun t _ => spatialEndpointFamily_measurable μ M s _
      ((T.left t).value_measurable Q ρ profile N σ J i S U))
    (fun t _ => spatialEndpointFamily_measurable ν P s _
      (continuous_star.measurable.comp ((T.right t).value_measurable Q ρ profile N σ J i S U)))
    (fun _ => C₀*μ.real univ/M) (fun _ => C₀*ν.real univ/P)
    (fun _ _ => div_nonneg (mul_nonneg hC₀ measureReal_nonneg) hM.le)
    (fun _ _ => div_nonneg (mul_nonneg hC₀ measureReal_nonneg) hP.le)
    (fun t _ => spatialEndpointFamily_norm_le μ hM s _
      ((T.left t).value_norm_le Q ρ profile N σ J i S hF hU))
    (fun t _ => spatialEndpointFamily_norm_le ν hP s _
      (fun x w => (norm_star _).le.trans
        ((T.right t).value_norm_le Q ρ profile N σ J i S hG hU x w)))
    c C
    (fun _ => jetStateEnvelope (m+1) (K+2*j) R D F G Q ρ profile N σ J i S U μ ν M P a v Ψ)
    (fun t _ => hc t) (fun t _ => hC t)
  · exact hcC.mono (fun r hr t _ => hr t)
  · intro t _
    exact spatial_endpoint_energy_le_jetStateEnvelope Q ρ profile N σ J i S hF hG hU μ ν
      hM hP s a v Ψ (T.left t) (T.right t)

end DescriptorInverseSymbols
end Falconer

end OAI
