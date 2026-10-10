import OAI.NumberTheory.DirichletL.Moments.FirstEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstSectors

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentCompleteCommon
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentActive CenteredMomentFourier IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def originalKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K)

theorem energy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
            originalKernel q.1 q.2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  have hspan (I : supportedColumns S) : Ideal.span {sourceGenerator S I} = I :=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp_rw [hspan]
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K)=_
  let F := fun I J : Ideal O =>
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem sector_independent_columns (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
              originalKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

def fixedFirstSum (C D : Ideal O) (hC : Supported C) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let k := K/‖eisEmbedding e‖^2
    let r := activeConductor C D
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) e*
      (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter a ha)
          (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) h*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2))

theorem originalKernel_fixed_first (C D : Ideal O) (hC : Supported C) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    originalKernel (C*Ideal.span {a}) (D*Ideal.span {b}) W K=fixedFirstSum C D hC a b ha hb W K := by
  let := finite_quotient_span (supported_element_ne_zero b hb)
  obtain ⟨h₁,h₂⟩ := fixed_common_parts C D hC.1 hD hCD
  have he := common_residual_reduced_poisson (fun P : CommonIndex C D => P.val) Subtype.val_injective
    (common_good C D hC) (common_odd C D hC) Finset.univ (leftExponent C D) (rightExponent C D)
    (fun P _ => ne_of_gt (leftExponent_pos C D P)) (fun P _ => ne_of_gt (rightExponent_pos C D P))
    a b (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ W K hK
  change _=fixedFirstSum C D hC a b ha hb W K at he
  rw [← he]
  unfold originalKernel
  apply tsum_congr
  intro z
  rw [← MulChar.star_apply',supportedModulusCharacter_mk,supportedModulusCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product,h₁,h₂]
  simp only [map_mul,star_mul]
  ring

end SevenEighths.CenteredMomentFirstSectorEnergy

end

end OAI
