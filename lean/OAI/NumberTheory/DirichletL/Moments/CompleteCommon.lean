import OAI.NumberTheory.DirichletL.Moments.Support
import OAI.NumberTheory.DirichletL.Moments.RankinRadical
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def commonSupport (I J : Ideal O) : Finset (Ideal O) := primeSupport I ∩ primeSupport J

def commonPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ commonSupport I J, P ^ valuation I P

def residualPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I \ primeSupport J, P ^ valuation I P

theorem commonSupport_comm (I J : Ideal O) : commonSupport I J = commonSupport J I :=
  Finset.inter_comm _ _

theorem supportExtract_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportExtract I S = ∏ P ∈ primeSupport I ∩ S, P ^ valuation I P := by
  unfold supportExtract
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I ∩ S) (by
    intro P hP
    exact Finset.mem_inter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_inter.mp hP).2, ↓reduceIte]
  rfl

theorem supportResidual_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportResidual I S = ∏ P ∈ primeSupport I \ S, P ^ valuation I P := by
  unfold supportResidual
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I \ S) (by
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_sdiff.mp hP).2]
  rfl

theorem commonPart_eq_supportExtract (I J : Ideal O) :
    commonPart I J = supportExtract I (commonSupport I J) := by
  rw [supportExtract_eq_power_product]
  simp only [commonPart, commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem residualPart_eq_supportResidual (I J : Ideal O) :
    residualPart I J = supportResidual I (commonSupport I J) := by
  rw [supportResidual_eq_power_product]
  have he : primeSupport I \ commonSupport I J = primeSupport I \ primeSupport J := by
    ext P
    simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
    tauto
  rw [he]
  rfl

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem residualPart_ne_zero (I J : Ideal O) : residualPart I J ≠ 0 := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_ne_zero _ _

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem commonPart_support (I J : Ideal O) :
    primeSupport (commonPart I J) = commonSupport I J := by
  rw [commonPart_eq_supportExtract, supportExtract_support]
  simp only [commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem commonParts_equal_support (I J : Ideal O) :
    primeSupport (commonPart I J) = primeSupport (commonPart J I) := by
  rw [commonPart_support, commonPart_support, commonSupport_comm I J]

theorem residualPart_support (I J : Ideal O) :
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J := by
  rw [residualPart_eq_supportResidual, supportResidual_support]
  ext P
  simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
  tauto

theorem commonPart_valuation (I J P : Ideal O) :
    valuation (commonPart I J) P = if P ∈ commonSupport I J then valuation I P else 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_count I P _

theorem residualPart_valuation (I J P : Ideal O) :
    valuation (residualPart I J) P = if P ∈ commonSupport I J then 0 else valuation I P := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_count I P _

theorem commonPart_residualPart_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart J I) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact extracted_residual_coprime I J _

theorem commonPart_own_residual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart I J) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact extracted_residual_coprime I I _

theorem commonProduct_leftResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) :=
  (commonPart_own_residual_coprime I J).mul_left (commonPart_residualPart_coprime J I)

theorem commonProduct_rightResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) :=
  (commonPart_residualPart_coprime I J).mul_left (commonPart_own_residual_coprime J I)

theorem residualParts_coprime (I J : Ideal O) :
    IsCoprime (residualPart I J) (residualPart J I) := by
  rw [residualPart_eq_supportResidual, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact common_support_residual_coprime I J

theorem canonical_complete_extraction (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = commonPart I J * residualPart I J ∧
    J = commonPart J I * residualPart J I ∧
    commonPart I J ≠ 0 ∧ commonPart J I ≠ 0 ∧
    residualPart I J ≠ 0 ∧ residualPart J I ≠ 0 ∧
    primeSupport (commonPart I J) = commonSupport I J ∧
    primeSupport (commonPart J I) = commonSupport I J ∧
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J ∧
    primeSupport (residualPart J I) = primeSupport J \ primeSupport I ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) ∧
    IsCoprime (residualPart I J) (residualPart J I) := by
  exact ⟨reconstruct I J hI, reconstruct J I hJ,
    commonPart_ne_zero I J, commonPart_ne_zero J I,
    residualPart_ne_zero I J, residualPart_ne_zero J I,
    commonPart_support I J, (commonPart_support J I).trans (commonSupport_comm J I),
    residualPart_support I J, residualPart_support J I,
    commonProduct_leftResidual_coprime I J, commonProduct_rightResidual_coprime I J,
    residualParts_coprime I J⟩

theorem commonPart_dvd (I J : Ideal O) (hI : I ≠ 0) : commonPart I J ∣ I :=
  ⟨residualPart I J, reconstruct I J hI⟩

theorem residualPart_dvd (I J : Ideal O) (hI : I ≠ 0) : residualPart I J ∣ I :=
  ⟨commonPart I J, (reconstruct I J hI).trans (mul_comm _ _)⟩

theorem residualPart_original_coprime (I J : Ideal O) (hJ : J ≠ 0) :
    IsCoprime (residualPart I J) J := by
  conv_rhs => rw [reconstruct J I hJ]
  exact (commonPart_residualPart_coprime J I).symm.mul_right (residualParts_coprime I J)

theorem commonPart_eq_one_of_empty (I J : Ideal O) (h : commonSupport I J = ∅) :
    commonPart I J = 1 := by simp only [commonPart, h, Finset.prod_empty]

theorem residualPart_eq_of_empty (I J : Ideal O) (hI : I ≠ 0)
    (h : commonSupport I J = ∅) : residualPart I J = I := by
  have he := reconstruct I J hI
  rw [commonPart_eq_one_of_empty I J h, one_mul] at he
  exact he.symm

theorem commonSupport_empty_iff (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    commonSupport I J = ∅ ↔ IsCoprime I J := by
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hJ,
    Finset.disjoint_iff_inter_eq_empty]
  rfl

theorem commonPart_one_right (I : Ideal O) : commonPart I 1 = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem commonPart_one_left (J : Ideal O) : commonPart 1 J = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_inter]

theorem residualPart_one_right (I : Ideal O) (hI : I ≠ 0) : residualPart I 1 = I := by
  apply residualPart_eq_of_empty I 1 hI
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem residualPart_one_left (J : Ideal O) : residualPart 1 J = 1 := by
  simp only [residualPart, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_sdiff, Finset.prod_empty]

theorem extracted_commonRadical (I J : Ideal O) :
    commonRadical (commonPart I J) (commonPart J I) = commonRadical I J := by
  unfold commonRadical
  rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
  rfl

theorem commonRadical_dvd_commonPart (I J : Ideal O) : commonRadical I J ∣ commonPart I J := by
  apply support_product_dvd (commonPart_ne_zero I J)
  rw [commonPart_support]
  exact Finset.Subset.refl _

theorem squarefree_mask_survives (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J ∧ s ∣ commonPart I J ∧ s ∣ commonPart J I ∧
      IsCoprime s (residualPart I J) ∧ IsCoprime s (residualPart J I) := by
  have hR := old_mask_dvd_commonRadical s I J hs hI hJ hsI hsJ
  have hC := hR.trans (commonRadical_dvd_commonPart I J)
  have hD : s ∣ commonPart J I := by
    have he : commonRadical I J = commonRadical J I := by
      simp only [commonRadical, Finset.inter_comm]
    exact (he ▸ hR).trans (commonRadical_dvd_commonPart J I)
  exact ⟨hR, hC, hD,
    (commonPart_own_residual_coprime I J).of_isCoprime_of_dvd_left hC,
    (commonPart_own_residual_coprime J I).of_isCoprime_of_dvd_left hD⟩

theorem commonPart_supported (I J : Ideal O) (hI : Supported I) : Supported (commonPart I J) := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_supported I hI _

theorem residualPart_supported (I J : Ideal O) (hI : Supported I) : Supported (residualPart I J) := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_supported I hI _

theorem primaryGenerator_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    CompletedGauss.primaryGenerator I =
      CompletedGauss.primaryGenerator (commonPart I J) *
        CompletedGauss.primaryGenerator (residualPart I J) := by
  rw [← CompletedGauss.primaryGenerator_mul, ← reconstruct I J hI]

theorem primary_complete_extraction (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let C := CompletedGauss.primaryGenerator (commonPart I J)
    let D := CompletedGauss.primaryGenerator (commonPart J I)
    let a := CompletedGauss.primaryGenerator (residualPart I J)
    let b := CompletedGauss.primaryGenerator (residualPart J I)
    CompletedGauss.primaryGenerator I = C * a ∧
    CompletedGauss.primaryGenerator J = D * b ∧
    IsCoprime (C * D) a ∧ IsCoprime (C * D) b ∧ IsCoprime a b := by
  dsimp only
  have hC := commonPart_supported I J hI
  have hD := commonPart_supported J I hJ
  have ha := residualPart_supported I J hI
  have hb := residualPart_supported J I hJ
  have hpC := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hC)
  have hpD := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hD)
  have hpa := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ ha)
  have hpb := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hb)
  refine ⟨primaryGenerator_reconstruct I J hI.1, primaryGenerator_reconstruct J I hJ.1, ?_, ?_, ?_⟩
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpa.1]
    exact commonProduct_leftResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpb.1]
    exact commonProduct_rightResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpa.1, hpb.1]
    exact residualParts_coprime I J

theorem common_valuations_pos (I J P : Ideal O) (hP : P ∈ commonSupport I J) :
    0 < valuation I P ∧ 0 < valuation J P := by
  obtain ⟨hI, hJ⟩ := Finset.mem_inter.mp hP
  exact ⟨Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hI),
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hJ)⟩

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

theorem absNorm_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm I = Ideal.absNorm (commonPart I J) * Ideal.absNorm (residualPart I J) := by
  have h := congrArg Ideal.absNorm (reconstruct I J hI)
  simpa only [map_mul] using h

theorem absNorm_commonPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (commonPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (commonPart_dvd I J hI))

theorem absNorm_residualPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (residualPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (residualPart_dvd I J hI))

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
