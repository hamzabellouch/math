import OAI.MeasureTheory.Falconer.Shells.InverseClassShell

namespace OAI

/-! # The original pair inverse controlled by the next recursive state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

noncomputable def pairIntegral (_T : DescriptorInverseSymbols f g j R A B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag s : ℝ) (μ ν : Measure (Space (m+3))) (M P r : ℝ) : ℂ :=
  (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q ρ profile N σ J i S Af z.1 t *
              g.ambient Q ρ profile N σ J i S Ag z.2 t) j w
        ∂sphereMeasure (m+3) ∂μ.prod ν

theorem original_pair_shell_le (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (γ : ℝ → ℂ) (hγ : Measurable γ) (C : DescriptorInverseIndex f g j → ℝ)
    (hC : ∀ t, 0 ≤ C t)
    (hγC : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ, ∀ t,
      ‖γ r*(T.coefficient N σ Af Ag U U t : ℂ)‖ ≤ C t) :
    (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖γ r*T.pairIntegral Q ρ profile N σ J i S Af Ag s μ ν M P r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (Fintype.card (DescriptorInverseIndex f g j) : ℝ)*
        ∑ t : DescriptorInverseIndex f g j, (C t)^2*
          ((spatialFourierCost (d := m+3) δ W hδ hW j)^2*
            jetStateEnvelope (m+1) (K+2*j) R D F G Q ρ profile N σ J i S U μ ν M P a v Ψ) := by
  have he : (fun r => γ r*T.pairIntegral Q ρ profile N σ J i S Af Ag s μ ν M P r) =
      fun r => ∑ t : DescriptorInverseIndex f g j,
        (γ r*(T.coefficient N σ Af Ag U U t : ℂ))*
          spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
            (spatialEndpointFamily μ M s ((T.left t).value Q ρ profile N σ J i S U))
            (spatialEndpointFamily ν P s
              (fun x w => star ((T.right t).value Q ρ profile N σ J i S U x w))) r := by
    funext r
    rw [pairIntegral,T.integration hD hA hB Q ρ profile N σ J i S hF hG Af Ag hU hU
      δ W hδ hW hs μ ν hsep M P r,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  change (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
    (∫ r, ‖(fun r => γ r*T.pairIntegral Q ρ profile N σ J i S Af Ag s μ ν M P r) r‖^2
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤ _
  rw [he]
  exact T.finite_shell_le Q ρ profile N σ J i S hF hG hU μ ν hM hP s a v Ψ
    δ W hδ hW (fun t r => γ r*(T.coefficient N σ Af Ag U U t : ℂ)) C
    (fun _ => hγ.mul_const _) hC hγC

end DescriptorInverseSymbols
end Falconer

end OAI
