import OAI.NumberTheory.DirichletL.Descent.FirstUnequalPhysicalEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι κ : Type*} [DecidableEq ι]
theorem actual_first_moving_family_two_energies
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro p hp _ hg source F selector C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep hω₁ hω₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

end
end SevenEighths.InverseMoment

end OAI
