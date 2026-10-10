import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCommon
import OAI.NumberTheory.DirichletL.Descent.FirstFreshMeasure

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation MeasureTheory
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev FirstCommonIndex (ι : Type*) :=
  (RayCharacter × RayCharacter) × (Σ _ : Finset ι, Finset ι × Finset ι)

def firstCommonIndices {ι : Type*} [DecidableEq ι] (F : Finset ι) : Finset (FirstCommonIndex ι) :=
  Finset.univ ×ˢ F.powerset.sigma (fun D => (F\D).powerset ×ˢ (F\D).powerset)

def firstCommonNorms {ι : Type*} (p : ι → Eis) (A₁ A₂ C R : ℝ) (d h : Eis)
    (j : FirstCommonIndex ι) : Fin 9 → ℝ :=
  ![A₁,A₂,C,‖eisEmbedding d‖^2,R,primeProductNorm p j.2.1,
    ‖eisEmbedding h‖^2,primeProductNorm p j.2.2.1,primeProductNorm p j.2.2.2]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonWeight (C₁ C₂ : Finset ι → ℂ) (h : Eis) (j : FirstCommonIndex ι) : ℂ :=
  crossCoeff j.1.1 j.1.2 * supportMobius (fun i => Ideal.span {p i}) j.2.1 *
    rowCoprimeMask (fun i => Ideal.span {p i}) j.2.1 h *
    firstCommonCoefficient p hg C₁ C₂ j.1 j.2.1 j.2.2.1 j.2.2.2 h

theorem firstPhysicalCommonRows_indexed (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    ∑ j ∈ firstCommonIndices F, firstCommonWeight p hg C₁ C₂ h j *
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j) := by
  simp only [firstPhysicalCommonRows,firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonNorms,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  ring

theorem firstPhysicalCommonRows_integral (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis)
    (s : Fin 9 → ℝ) (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ firstCommonIndices F,
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K
        (firstCommonNorms p A₁ A₂ C R d h j) =
      (firstRootScale s:ℂ)⁻¹ *
        (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
        ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) :
    firstPhysicalCommonRows p hg F C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹ * ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
      ∑ j ∈ firstCommonIndices F,firstCommonWeight p hg C₁ C₂ h j *
        (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 := by
  rw [firstPhysicalCommonRows_indexed]
  calc
    _ = (firstRootScale s:ℂ)⁻¹ * ∑ j ∈ firstCommonIndices F,
        (firstCommonWeight p hg C₁ C₂ h j *
          (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8))) *
        ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j hj]
      ring
    _ = _ := by
      rw [full_density_finite_sum]

end
end SevenEighths.InverseMoment

end OAI
