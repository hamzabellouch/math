import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

theorem supportExtract_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem supportExtract_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportResidual_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportResidual I S)).count P =
      if P ∈ S then 0 else (normalizedFactors I).count P := by
  rw [supportResidual_factors, Multiset.count_filter]
  split_ifs <;> rfl

theorem supportExtract_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportExtract I S) := by
  refine ⟨supportExtract_ne_zero I S, ?_⟩
  intro P hP
  rw [supportExtract_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem supportResidual_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportResidual I S) := by
  refine ⟨supportResidual_ne_zero I S, ?_⟩
  intro P hP
  rw [supportResidual_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem extracted_residual_coprime (I J : Ideal O) (S : Finset (Ideal O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    intro P hP hQ
    exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)

theorem common_support_residual_coprime (I J : Ideal O) :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact (Finset.mem_sdiff.mp hP).2
    (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hP).1, (Finset.mem_sdiff.mp hQ).1⟩)

theorem supportExtract_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [supportResidual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportResidual_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportResidual P S = if P ∈ S then 1 else P := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportResidual, hf, Multiset.filter_singleton]
  split_ifs <;> simp_all

theorem shared_prime_slot_freeze (P I : Ideal O) (hP : Prime P) (hI : I ≠ 0)
    (S : Finset (Ideal O)) (hPS : P ∈ S) :
    supportExtract (P * I) S = P * supportExtract I S ∧
      supportResidual (P * I) S = supportResidual I S := by
  rw [supportExtract_mul P I hP.ne_zero hI S, supportResidual_mul P I hP.ne_zero hI S,
    supportExtract_prime P hP S, supportResidual_prime P hP S]
  simp only [hPS, ite_true, one_mul, and_self]

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

def idealCorrelation (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (j : O) : ℂ :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

theorem idealCorrelation_complete_extraction (I J : Ideal O)
    (hI : Supported I) (hJ : Supported J) (j : O) :
    let S := primeSupport I ∩ primeSupport J
    let D := supportExtract I S
    let E := supportExtract J S
    let A := supportResidual I S
    let B := supportResidual J S
    idealCorrelation I J hI hJ j =
      idealCorrelation D E (supportExtract_supported I hI S) (supportExtract_supported J hJ S) j *
        sexticReciprocityPhase (primaryGenerator A) (primaryGenerator E) *
        star (sexticReciprocityPhase (primaryGenerator B) (primaryGenerator D)) *
        sexticReciprocityPhase (primaryGenerator A) (primaryGenerator B) *
        idealRowHom j A * star (idealRowHom (-j) B) := by
  let S := primeSupport I ∩ primeSupport J
  let D := supportExtract I S
  let E := supportExtract J S
  let A := supportResidual I S
  let B := supportResidual J S
  have hD := supportExtract_supported I hI S
  have hE := supportExtract_supported J hJ S
  have hA := supportResidual_supported I hI S
  have hB := supportResidual_supported J hJ S
  have hpD := primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)
  have hpE := primaryGenerator_spec E (supported_primaryGenerator_ne_zero E hE)
  have hpA := primaryGenerator_spec A (supported_primaryGenerator_ne_zero A hA)
  have hpB := primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)
  have hcpA : IsCoprime (primaryGenerator D * primaryGenerator E) (primaryGenerator A) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpD.1, hpE.1, hpA.1]
    exact (extracted_residual_coprime I I S).mul_left (extracted_residual_coprime J I S)
  have hcpB : IsCoprime (primaryGenerator D * primaryGenerator E) (primaryGenerator B) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpD.1, hpE.1, hpB.1]
    exact (extracted_residual_coprime I J S).mul_left (extracted_residual_coprime J J S)
  have hcpAB : IsCoprime (primaryGenerator A) (primaryGenerator B) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpA.1, hpB.1]
    exact common_support_residual_coprime I J
  have h := actual_complete_common_support
    (primaryGenerator D) (primaryGenerator E) (primaryGenerator A) (primaryGenerator B)
    ((supported_span_primaryGenerator_iff D).mpr hD)
    ((supported_span_primaryGenerator_iff E).mpr hE)
    ((supported_span_primaryGenerator_iff A).mpr hA)
    ((supported_span_primaryGenerator_iff B).mpr hB)
    hpD.2 hpE.2 hpA.2 hpB.2 hcpA hcpB hcpAB j
  have hDA : D * A = I := support_reconstruct I hI.1 S
  have hEB : E * B = J := support_reconstruct J hJ.1 S
  simpa only [completeSupportExtension, ← primaryGenerator_mul, hDA, hEB, hpA.1, hpB.1,
    idealCorrelation] using h

end SevenEighths.CenteredMomentSupport
end

end OAI
