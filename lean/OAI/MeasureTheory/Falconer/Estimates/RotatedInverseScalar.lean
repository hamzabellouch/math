import OAI.MeasureTheory.Falconer.Shells.RotatedInverseShell
import OAI.MeasureTheory.Falconer.Estimates.ScalarInverseTransfer

namespace OAI

/-! # Scalar Fourier transfer for the rotated inverse on the original laws -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem rotated_inverse_normalized_sum_eq {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P a v r : ℝ) :
    ((M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
        (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) ∂μ.prod ν)) /
      (((2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) : ℝ) : ℂ) =
      rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
        U δ W hδ hW s μ ν M P a v r := by
  rw [rotated_inverse_jet_integration k A H hA Q ρ profile N σ J i S hF hU δ hδ s μ ν (hsep.mono fun _ hz => hz.1) M P r,Finset.sum_div]
  unfold rotatedInverseNormalizedSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rotatedScaledInverseTerm]
  rw [(H j).integration (hA j) Q ρ profile N σ J i S hF hU
      δ W hδ hW hs μ ν hsep M P r,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Complex.ofReal_div,Complex.ofReal_mul]
  ring


theorem scalar_shell_of_rotated_inverse {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    {s : ℝ} (hs : 0 < s) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (Qhat : ℝ → ℂ) (hQhat : Measurable Qhat) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖Qhat r-(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
        rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
          (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) ∂μ.prod ν)‖ ≤ ε) :
    IntegrableOn (fun r => ‖Qhat r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖Qhat r‖^2) ≤
        2*(rotatedInverseShellCost m k F A U δ W hδ hW *
          jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hi := rotated_inverse_family_shell_integrable k A H Q ρ profile N σ J i S
    hF hU hE hFE δ W hδ hW s μ ν hM hP a v Ψ hregime
  have hb := rotated_inverse_family_shell_le k A H Q ρ profile N σ J i S
    hF hU hE hFE δ W hδ hW s μ ν hM hP a v Ψ hregime
  have hb' : (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)) *
      (∫ r, ‖rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
        U δ W hδ hW s μ ν M P a v r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      rotatedInverseShellCost m k F A U δ W hδ hW *
        jetStateEnvelope (m+1) (2*k) L 1 F F Q ρ profile N σ J i S U μ ν M P a v Ψ := by
    apply hb.trans_eq
    unfold rotatedInverseShellCost
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  apply scalar_shell_of_stationary_approximation (m+3) a v Ψ hΨ hpos hzero hone Qhat
    (rotatedInverseNormalizedSum k A H Q ρ profile N σ J i S
      U δ W hδ hW s μ ν M P a v) hQhat hi _ hb'
  filter_upwards [herr] with r hr
  rw [← rotated_inverse_normalized_sum_eq k A H hA Q ρ profile N σ J i S
    hF hU δ W hδ hW hs μ ν hsep M P a v r]
  have he : (v-a)*(((m+3:ℕ):ℝ)-1)/2 = (v-a)*(((m+2:ℕ):ℝ)/2) := by
    push_cast
    ring
  rw [he,mul_div_cancel₀ _ (by exact_mod_cast
    (ne_of_gt (show 0 < (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2)) by positivity)))]
  exact hr

end Falconer

end OAI
