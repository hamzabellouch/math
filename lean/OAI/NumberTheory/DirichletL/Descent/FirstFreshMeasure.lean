import OAI.NumberTheory.DirichletL.Descent.FirstNominal
import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory JointLogSeparation
noncomputable section

def firstRelativeLog (q s : Fin 9 → ℝ) (i : Fin 9) : ℝ := Real.log (q i/s i)

theorem first_fresh_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs₁ : Function.support W₁ ⊆ Set.Icc lo hi) (hs₂ : Function.support W₂ ⊆ Set.Icc lo hi)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ,ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ s : Fin 9 → ℝ, (∀ i, 0 < s i) → ∀ K : ℝ, 0 < K → ∃ b₃ : 𝓢(ℝ,ℂ),
      (∀ (ω₁ ω₂ : ℝ → ℂ) (q : Fin 9 → ℝ), (∀ i, 0 < q i) →
        (W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → ω₁ (q 7/s 7) = 1) →
        (W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → ω₂ (q 8/s 8) = 1) →
        (ω₁ (q 7/s 7) ≠ 0 → ω₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) →
        firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
          (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
        (firstRootScale s:ℂ)⁻¹ * (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
          ∫ z : Frequency × (Fin 9 → ℝ),
            fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
            pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2) ∧
      Integrable (fun z : Frequency × (Fin 9 → ℝ) => tripleHeight J z.1*coordinateHeight J z.2*
        ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ∧
      (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^A *
        (∫ z : Frequency × (Fin 9 → ℝ), tripleHeight J z.1*coordinateHeight J z.2*
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hs⟩ := first_full_profile_common_measure
    W₁ W₂ lo hi hlo hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro s hspos K hK
  obtain ⟨b₃,he,hI,hB⟩ := hs (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))
    (div_pos (mul_pos hK (hspos 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hspos 3) (hspos 4))
        (sq_pos_of_pos (hspos 5))) (hspos 7)) (hspos 8)))
  refine ⟨b₃,?_,hI,hB⟩
  intro ω₁ ω₂ q hq hω₁ hω₂ hcut
  by_cases hw₁ : ω₁ (q 7/s 7) = 0
  · have hh : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0 := by
      by_contra hn
      have := hω₁ hn
      simp only [hw₁,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 8/s 8) = 0
  · have hh : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0 := by
      by_contra hn
      have := hω₂ hn
      simp only [hw₂,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₂,mul_zero,zero_mul,zero_div]
  have hcut' := hcut hw₁ hw₂
  have hnom := firstNormProfile_nominal W₁ W₂ Φ (fun _ _ => 1) s q hspos hq K
  have hfull : firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    rw [full_density_mode_fubini]
    rw [show firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
        firstPoissonProfile W₁ W₂ Φ V (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) from by
      unfold firstRelativeLog
      rw [firstPoissonProfile_log W₁ W₂ Φ V _ _ (fun i => div_pos (hq i) (hspos i))]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]]
    simpa only [pureProfileMode_height] using he (firstRelativeLog q s)
  have hm : firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
      (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q := by
    by_cases h1 : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0
    · simp only [firstNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0
    · simp only [firstNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm,hnom,hfull]
  ring

end
end SevenEighths.InverseMoment

end OAI
