import OAI.NumberTheory.DirichletL.Descent.SecondKernelMeasure

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem second_fresh_kernel_common_measure
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
      (∀ (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
        (W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1) →
        (W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1) →
        (ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
          ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) →
        secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
            ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
                (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
                  (t₁,t₂,t₃) u i) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i))) ∧
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
  intro ω₁ ω₂ q hq hω₁ hω₂ hcut
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      have hh := hω₁ hn
      rw [hw₁] at hh
      exact zero_ne_one hh
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      have hh := hω₂ hn
      rw [hw₂] at hh
      exact zero_ne_one hh
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
      secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
        (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm,he q hq (hcut hw₁ hw₂)]
  ring

end
end SevenEighths.InverseMoment

end OAI
