import OAI.NumberTheory.DirichletL.Descent.FirstBlocks
import OAI.NumberTheory.DirichletL.Descent.FirstProfileUniform

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open JointLogSeparation MeasureTheory
noncomputable section

theorem first_fresh_physical_profile
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (s q : Fin 9 → ℝ) (hspos : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (normalization : ℂ)
    (he : ∀ y : Fin 9 → ℝ, normalization * firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → ω₁ (q 7/s 7) = 1)
    (hω₂ : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → ω₂ (q 8/s 8) = 1)
    (hcut : ω₁ (q 7/s 7) ≠ 0 → ω₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) :
    normalization * firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
    (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
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
  have hfull : normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    have hp := firstPoissonProfile_log W₁ W₂ Φ V
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)
      (fun i => div_pos (hq i) (hspos i))
    have hc : firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) =
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) := by
      unfold firstRelativeLog
      rw [hp]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]
    rw [← hc]
    exact he (firstRelativeLog q s)
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
  calc
    _ = (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
        (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)) := by
      conv_lhs => rw [hm,hnom]
      ring
    _ = _ := by rw [hfull]

theorem first_balanced_density_integrable (g : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseMomentFirstProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

open ActualEisensteinCubic FirstPassCubeLabels
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem firstCommonNorms_pos (A₁ A₂ C R : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hC : 0 < C) (hR : 0 < R) (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0)
    (j : FirstCommonIndex ι) : ∀ i,0 < firstCommonNorms p A₁ A₂ C R d h j i := by
  intro i
  fin_cases i <;> simp only [firstCommonNorms]
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hd))
  · exact hR
  · exact primeProductNorm_pos p hp _
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh))
  · exact primeProductNorm_pos p hp _
  · exact primeProductNorm_pos p hp _

include hp in

theorem actual_first_balanced_block (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (A₁ A₂ C R K L : ℝ)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hC : 0 < C) (hR : 0 < R)
    (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0) (s : Fin 9 → ℝ) (hs : ∀ i,0 < s i)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F selector C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  apply first_block_normalized_density p hg F selector C₁ C₂ _ _ ω₁ ω₂ Φ A₁ A₂ C R K d h s density hDensity
  intro j hj hn
  exact first_fresh_physical_profile W₁ W₂ ω₁ ω₂ Φ V s
    (firstCommonNorms p A₁ A₂ C R d h j) hs
    (firstCommonNorms_pos p hp A₁ A₂ C R hA₁ hA₂ hC hR d h hd hh j) K density
    (Real.exp (-(9/2:ℝ)*L):ℂ) hsep
    (by simpa [firstCommonNorms] using hω₁ j hj hn)
    (by simpa [firstCommonNorms] using hω₂ j hj hn)
    (by simpa [firstCommonNorms] using hcut j hj hn)

end
end SevenEighths.InverseMoment

end OAI
