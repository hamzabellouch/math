import OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorTransform
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSupportedCorrelation IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem residualPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (a:Ideal O) := by
  have ha := (Finset.mem_filter.mp ((mem_residualPool C hC (supportedColumns S) a).mp a.property)).2
  exact ((supported_mul_iff C a).mp ha).2

def residualElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : O := CompletedGauss.primaryGenerator a

theorem residualElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Ideal.span {residualElement C hC S a}=a :=
  primary_span_supported a (residualPool_supported C hC S a)

theorem residualElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (Ideal.span {residualElement C hC S a}) := by
  rw [residualElement_span]
  exact residualPool_supported C hC S a

def sectorFixedTransform (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ a : residualPool C hC.1 (supportedColumns S),
    ∑ b : residualPool D hD.1 (supportedColumns S),
      if IsCoprime C (a:Ideal O) ∧ IsCoprime C (b:Ideal O) ∧ IsCoprime (a:Ideal O) (b:Ideal O) then
        ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
          fixedFirstSum C D hC (residualElement C hC.1 S a) (residualElement D hD.1 S b)
            (residualElement_supported C hC.1 S a) (residualElement_supported D hD.1 S b) W K
      else 0

theorem sector_fixed_transform (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        sectorFixedTransform η m A t S c C D hC hD W K := by
  rw [sector_independent_columns η m A t S c C D hC.1 hD.1 hCD W K]
  congr 1
  unfold sectorFixedTransform
  let F := fun a b : Ideal O =>
    if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
      ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*originalKernel (C*a) (D*b) W K else 0
  change (∑ a∈residualPool C hC.1 (supportedColumns S),∑ b∈residualPool D hD.1 (supportedColumns S),F a b)=_
  rw [← Finset.sum_coe_sort _ (fun a => ∑ b∈residualPool D hD.1 (supportedColumns S),F a b)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_coe_sort _ (F a)]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only [F]
  split_ifs
  · have hh := originalKernel_fixed_first C D hC hD.1 hCD
      (residualElement C hC.1 S a) (residualElement D hD.1 S b)
      (residualElement_supported C hC.1 S a) (residualElement_supported D hD.1 S b) W K hK
    rw [residualElement_span,residualElement_span] at hh
    rw [hh]
  · rfl

theorem commonLabels_supported (S : Finset (Ideal O))
    (p : commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported p.val.1 ∧ Supported p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
  have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
  rw [← he]
  exact ⟨commonPart_supported _ _ hq₁,commonPart_supported _ _ hq₂⟩

theorem energy_fixed_transforms (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          sectorFixedTransform η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K := by
  rw [energy_common_sectors η m A t hmLam hm2 S c W K hK]
  rw [← Finset.sum_coe_sort _ (fun p : Ideal O × Ideal O => ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
    ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K)]
  apply Finset.sum_congr rfl
  intro p hp
  exact sector_fixed_transform η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K hK

end SevenEighths.CenteredMomentFirstSectorTransform

end

end OAI
