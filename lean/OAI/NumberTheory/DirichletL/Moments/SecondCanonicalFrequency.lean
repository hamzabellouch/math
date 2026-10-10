import OAI.NumberTheory.DirichletL.Moments.SecondCanonical

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem commonFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    commonFrequencyGenerator C D∣primaryGenerator C ∧
    commonFrequencyGenerator C D∣primaryGenerator D := by
  rw [←left_generator_product C D hC hCD,←right_generator_product C D hC hD hCD]
  constructor
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>pow_dvd_pow _ (min_le_left _ _))
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>pow_dvd_pow _ (min_le_right _ _))

theorem idealCorrelation_zero_outside_common (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (j : O) (hj : ¬commonFrequencyGenerator C D∣j) : idealCorrelation C D hC hD j=0 := by
  have hd := commonFrequencyGenerator_dvd C D hC hD hCD
  let := finite_quotient_span (supported_primaryGenerator_ne_zero C hC)
  let := finite_quotient_span (supported_primaryGenerator_ne_zero D hD)
  let : Fintype (O⧸Ideal.span {primaryGenerator C}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {primaryGenerator D}) := Fintype.ofFinite _
  unfold idealCorrelation actualCorrelation
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ _ _ _ _ hd.1 hd.2 hj

theorem idealCorrelation_tsum_common (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (F : O→ℂ) :
    (∑' j : O,idealCorrelation C D hC hD j*F j)=
      ∑' w : O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*
        F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq (f := fun j => idealCorrelation C D hC hD j*F j) ?_
  intro j hj
  have hd : commonFrequencyGenerator C D∣j := by
    by_contra hn
    exact hj (by dsimp only;rw [idealCorrelation_zero_outside_common C D hC hD hCD j hn,zero_mul])
  obtain ⟨w,hw⟩ := hd
  exact ⟨w,hw.symm⟩

def canonicalPartition (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : Prop :=
  actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U

def canonicalPartitionScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : ℂ :=
  if canonicalPartition C D U w then
    (partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U:ℂ)⁻¹ else 0

theorem actual_ideal_partition_scalar (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O) :
    ‖canonicalPartitionScalar C D U w*
      idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)‖≤1 := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hg (P : CommonIndex C D) : goodLambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P];exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P];exact common_odd C D hC P
  have hp : canonicalPartition C D U w→∀ i∈U,
      leftExponent C D i=rightExponent C D i ∧ ¬6∣leftExponent C D i ∧
        ¬commonPrime C D i∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w i := by
    intro h i hi
    rw [canonicalPartition] at h
    rw [←h] at hi
    exact (Finset.mem_filter.mp hi).2
  have hh := normalized_partition_norm_le_one (commonPrime C D) (commonPrime_supported C D hC)
    hg hc (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) U (canonicalPartition C D U) w hp
  simp only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD] at hh
  by_cases hw : canonicalPartition C D U w
  · simpa only [canonicalPartitionScalar,ite_eq_left hw,div_eq_mul_inv,mul_comm,
      idealCorrelation,commonFrequencyGenerator] using hh
  · simp only [canonicalPartitionScalar,ite_eq_right hw,zero_mul,norm_zero,zero_le_one]

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
