import OAI.MeasureTheory.Falconer.Shells.TwoProfileInverseShell
import OAI.MeasureTheory.Falconer.Estimates.ScalarInverseTransfer

namespace OAI

/-! # Returning the exact inverse jet shell to the scalar Fourier integral -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem two_profile_inverse_normalized_sum_eq {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D} (k R : ℕ)
    (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P a v r : ℝ) :
    ((M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      scaledWeightedInverseSum m k s r (z.1-z.2)
        (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
          g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν)) /
      (((2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) : ℝ) : ℂ) =
      twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
        Af Ag U δ W hδ hW s μ ν M P a v r := by
  rw [two_profile_scaled_inverse_integration k R A B T hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG
    Af Ag hU δ hδ s μ ν (hsep.mono fun _ hz => hz.1) M P r,Finset.sum_div]
  unfold twoProfileInverseNormalizedSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [DescriptorInverseSymbols.twoProfilePairIntegral,
    (T j).two_profile_integration hD (hA j) (hB j) Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG Af Ag hU hU
      δ W hδ hW hs μ ν hsep M P r,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Complex.ofReal_div,Complex.ofReal_mul]
  ring

theorem scalar_shell_of_two_profile_inverse {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    {s : ℝ} (hs : 0 < s) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (energy : ℝ)
    (henergy : ∀ (u : DescriptorJetSymbol (m+1) (K+2*k) R F D)
      (w : DescriptorJetSymbol (m+1) (K+2*k) R G D),
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
        (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy)
    (H : ℝ → ℂ) (hH : Measurable H) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖H r-(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
        scaledWeightedInverseSum m k s r (z.1-z.2)
          (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
            g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν)‖ ≤ ε) :
    IntegrableOn (fun r => ‖H r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖H r‖^2) ≤
        2*(descriptorInverseShellCost f g k A B Af Ag U δ W hδ hW *
          energy) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hi := two_profile_inverse_family_shell_integrable k R A B T hD Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
    hF hG Af Ag hU hE hDE hFE hGE δ W hδ hW s μ ν hM hP a v Ψ hregime
  have hb := two_profile_inverse_family_shell_le k R A B T hD Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
    hF hG Af Ag hU hE hDE hFE hGE δ W hδ hW s μ ν hM hP a v Ψ hregime energy henergy
  have hb' : (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
        Af Ag U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      descriptorInverseShellCost f g k A B Af Ag U δ W hδ hW *
        energy := by
    apply hb.trans_eq
    unfold descriptorInverseShellCost
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  apply scalar_shell_of_stationary_approximation (m+3) a v Ψ hΨ hpos hzero hone H
    (twoProfileInverseNormalizedSum k R A B T Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
      Af Ag U δ W hδ hW s μ ν M P a v) hH hi _ hb'
  filter_upwards [herr] with r hr
  rw [← two_profile_inverse_normalized_sum_eq k R A B T hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂
    hF hG Af Ag hU δ W hδ hW hs μ ν hsep M P a v r]
  have he : (v-a)*(((m+3:ℕ):ℝ)-1)/2 = (v-a)*(((m+2:ℕ):ℝ)/2) := by
    push_cast
    ring
  rw [he,mul_div_cancel₀ _ (by exact_mod_cast
    (ne_of_gt (show 0 < (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) by positivity)))]
  exact hr

end Falconer

end OAI
