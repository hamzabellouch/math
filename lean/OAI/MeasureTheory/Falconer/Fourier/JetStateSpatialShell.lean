import OAI.MeasureTheory.Falconer.Estimates.InverseClassExpansion
import OAI.MeasureTheory.Falconer.Fourier.JetStateOperations
import OAI.MeasureTheory.Falconer.Fourier.JetStateEnvelope
import OAI.MeasureTheory.Falconer.Estimates.SpatialEndpointFamily
import OAI.MeasureTheory.Falconer.Shells.FiniteSpatialShell

namespace OAI

/-! # Spatial Fourier terms controlled by the exact recursive state

Spatial phases and conjugation preserve the actual descriptor symbol
class. Consequently each separated inverse factor is controlled by its
own next-state supremum, without enlarging the class of angular symbols.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def spatialFourier (f : DescriptorJetSymbol n K L F D)
    (s : ℝ) (ξ : Space (n+2)) : DescriptorJetSymbol n K L F D :=
  f.spatialMultiplier (spatialFourierPhase s ξ) (by fun_prop)
    (fun x => (spatialFourierPhase_norm s ξ x).le)

theorem spatialFourier_value (f : DescriptorJetSymbol n K L F D)
    (s : ℝ) (ξ : Space (n+2))
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    (f.spatialFourier s ξ).value Q ρ profile N σ J i S A x w =
      spatialFourierPhase s ξ x*f.value Q ρ profile N σ J i S A x w :=
  f.spatialMultiplier_value _ _ _ Q ρ profile N σ J i S A x w

end DescriptorJetSymbol

theorem spatial_endpoint_energy_le_jetStateEnvelope
    {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (s a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D)
    (ξ : Space (n+2)) :
    independentAngularEnergy a v Ψ
      (fun p => spatialEndpointFamily μ M s (f.value Q ρ profile N σ J i S A) (ξ,p))
      (fun p => spatialEndpointFamily ν P s
        (fun x w => star (g.value Q ρ profile N σ J i S A x w)) (ξ,p)) ≤
      jetStateEnvelope n K L D F G Q ρ profile N σ J i S A μ ν M P a v Ψ := by
  have h := jetStateEnergy_le_envelope Q ρ profile N σ J i S hF hG hA μ ν hM hP
    a v Ψ (f.spatialFourier s ξ) (g.conj.spatialFourier s ξ)
  have hf : (f.spatialFourier s ξ).value Q ρ profile N σ J i S A =
      fun x w => spatialFourierPhase s ξ x*f.value Q ρ profile N σ J i S A x w := by
    funext x w
    exact f.spatialFourier_value s ξ Q ρ profile N σ J i S A x w
  have hg : (g.conj.spatialFourier s ξ).value Q ρ profile N σ J i S A =
      fun x w => spatialFourierPhase s ξ x*star (g.value Q ρ profile N σ J i S A x w) := by
    funext x w
    rw [DescriptorJetSymbol.spatialFourier_value,DescriptorJetSymbol.conj_value]
  simpa only [jetStateEnergy,hf,hg,spatialEndpointFamily] using h

theorem jet_state_spatial_shell_le
    {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (s a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) (j : ℕ) :
    (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
        (spatialEndpointFamily μ M s (f.value Q ρ profile N σ J i S A))
        (spatialEndpointFamily ν P s (fun x w => star (g.value Q ρ profile N σ J i S A x w))) r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (spatialFourierCost (d := n+2) δ W hδ hW j)^2*
        jetStateEnvelope n K L D F G Q ρ profile N σ J i S A μ ν M P a v Ψ := by
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*A⁻¹ := by
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hA.le)
  apply spatial_endpoint_shared_shell_le μ ν hM hP s a v Ψ
    (f.value Q ρ profile N σ J i S A)
    (fun x w => star (g.value Q ρ profile N σ J i S A x w))
    (f.value_measurable Q ρ profile N σ J i S A)
    (continuous_star.measurable.comp (g.value_measurable Q ρ profile N σ J i S A))
    hbound hbound (f.value_norm_le Q ρ profile N σ J i S hF hA)
    (fun x w => (norm_star _).le.trans (g.value_norm_le Q ρ profile N σ J i S hG hA x w))
    δ W hδ hW j
  exact spatial_endpoint_energy_le_jetStateEnvelope Q ρ profile N σ J i S hF hG hA μ ν
    hM hP s a v Ψ f g

end Falconer

end OAI
