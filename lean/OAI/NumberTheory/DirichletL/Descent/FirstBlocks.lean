import OAI.NumberTheory.DirichletL.Descent.FirstCommonColumns
import OAI.NumberTheory.DirichletL.Descent.DensityAssembly

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstBlockedPhysicalRows (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ j ∈ firstCommonIndices F, selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j *
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j)

def firstBlockedSeparatedRow (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, selector D * supportMobius (fun i => Ideal.span {p i}) D *
      rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h

theorem first_block_modes_eq_columns (F : Finset ι) (selector : Finset ι → ℂ) (C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ j ∈ firstCommonIndices F,(selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j) *
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
      pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
        (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) =
    firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstBlockedSeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  calc
    _ = crossCoeff r.1 r.2 *
        (selector D * supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
          firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s)) *
        (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
          firstCommonCoefficient p hg C₁ C₂ r D U V h *
            (ω₁ (primeProductNorm p U/s 7)*ω₂ (primeProductNorm p V/s 8)) *
            logPhase (H 7) (Real.log (primeProductNorm p U/s 7)) *
            logPhase (H 8) (Real.log (primeProductNorm p V/s 8))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      rw [first_common_source_mode]
      dsimp only [H]
      ring
    _ = _ := by
      rw [firstCommonColumn_pair]
      dsimp only [H]
      ring

theorem first_blocks_reconstruct {κ : Type*} (blocks : Finset κ)
    (F : Finset ι) (selector : κ → Finset ι → ℂ)
    (hpartition : ∀ D ∈ F.powerset, ∑ a ∈ blocks, selector a D = 1)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) :
    (∑ a ∈ blocks, firstBlockedPhysicalRows p hg F (selector a) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h) =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  unfold firstBlockedPhysicalRows
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hDj : j.2.1 ∈ F.powerset := (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1
  rw [← Finset.sum_mul, ← Finset.sum_mul, hpartition j.2.1 hDj, one_mul]

def firstCommonBlockSelector {κ : Type*} [DecidableEq κ]
    (label : Finset ι → κ) (a : κ) (D : Finset ι) : ℂ :=
  if label D = a then 1 else 0

theorem first_source_blocks_reconstruct {κ : Type*} [DecidableEq κ]
    (F : Finset ι) (label : Finset ι → κ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) :
    (∑ a ∈ F.powerset.image label,
      firstBlockedPhysicalRows p hg F (firstCommonBlockSelector label a)
        C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h) =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  apply first_blocks_reconstruct
  intro D hD
  have hm : label D ∈ F.powerset.image label := Finset.mem_image_of_mem label hD
  simp [firstCommonBlockSelector,hm]

theorem first_block_nonzero_label {κ : Type*} [DecidableEq κ]
    (label : Finset ι → κ) (a : κ) (C₁ C₂ : Finset ι → ℂ) (h : Eis)
    (j : FirstCommonIndex ι)
    (hn : firstCommonBlockSelector label a j.2.1 * firstCommonWeight p hg C₁ C₂ h j ≠ 0) :
    label j.2.1 = a := by
  by_contra he
  simp [firstCommonBlockSelector,he] at hn

theorem first_block_normalized_density (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (normalization : ℂ)
    (he : ∀ j ∈ firstCommonIndices F,
      selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
        (firstCommonNorms p A₁ A₂ C R d h j) =
      (firstRootScale s:ℂ)⁻¹ *
        (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
        ∫ z : Frequency × (Fin 9 → ℝ),density z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) :
    normalization * firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹ * ∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp_rw [← first_block_modes_eq_columns]
  rw [← density_finite_sum _ density hDensity]
  simp only [firstBlockedPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j = 0
  · simp only [hz,zero_mul,mul_zero]
  · calc
      _ = (selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j) *
          (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
            (firstCommonNorms p A₁ A₂ C R d h j)) := by ring
      _ = _ := by rw [he j hj hz]; ring

end
end SevenEighths.InverseMoment

end OAI
