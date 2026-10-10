import OAI.NumberTheory.DirichletL.Descent.SecondKernelMeasure
import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

universe u

theorem second_finite_source_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ {κ : Type u} (source : Finset κ) (c : κ → ℂ) (q : κ → Fin 6 → ℝ),
        (∀ x ∈ source, ∀ i, 0 < q x i) →
        (∀ x ∈ source, ∀ i, V i (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀ i) = 1) →
        (∑ x ∈ source, c x * secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (q x)) =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
            ∫ p : Frequency × (Fin 6 → ℝ),
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
                ∑ x ∈ source, c x * pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
                  (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ source c q hq hcut
  have hpoint (x : κ) (hx : x ∈ source) :
      secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
        (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (q x) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ p : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2 := by
    rw [he (q x) (hq x hx) (hcut x hx),full_density_mode_fubini]
    simp only [pureProfileMode_height]
  calc
    _ = ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∑ x ∈ source, c x *
        ∫ p : Frequency × (Fin 6 → ℝ),
          fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpoint x hx]
      ring
    _ = _ := by rw [full_density_finite_sum]

end
end SevenEighths.InverseMoment

end OAI
