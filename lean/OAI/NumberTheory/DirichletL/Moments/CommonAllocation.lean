import OAI.NumberTheory.DirichletL.Moments.CommonSectors
import OAI.NumberTheory.DirichletL.Moments.HeckeExpansion

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocation
open CenteredMomentSupport CenteredMomentCommonSectors CenteredMomentExtraction
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem extract_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportExtract (C*a) (primeSupport C)=C := by
  rw [supportExtract_mul C a hC ha,
    supportExtract_of_subset C hC _ (Finset.Subset.refl _),
    supportExtract_of_disjoint a _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa).symm,
    mul_one]

theorem residual_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportResidual (C*a) (primeSupport C)=a := by
  apply mul_left_cancel₀ hC
  have he := support_reconstruct (C*a) (mul_ne_zero hC ha) (primeSupport C)
  rwa [extract_coprime_product C a hC ha hCa] at he

theorem tuple_products {ι : Type*} [Fintype ι] (v : ι → Ideal O) (C a : Ideal O)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hv : ∏ i,v i=C*a) :
    (∏ i,supportExtract (v i) (primeSupport C))=C ∧
      (∏ i,supportResidual (v i) (primeSupport C))=a := by
  have hv0 : ∏ i,v i≠0 := hv.symm ▸ mul_ne_zero hC ha
  have hi (i : ι) : v i≠0 := Finset.prod_ne_zero_iff.mp hv0 i (Finset.mem_univ _)
  constructor
  · rw [← supportExtract_prod Finset.univ v (fun i _ => hi i),hv]
    exact extract_coprime_product C a hC ha hCa
  · rw [← supportResidual_prod Finset.univ v (fun i _ => hi i),hv]
    exact residual_coprime_product C a hC ha hCa

theorem residual_factor_coprime (C I : Ideal O) (hC : C≠0) :
    IsCoprime C (supportResidual I (primeSupport C)) := by
  have hh := extracted_residual_coprime C I (primeSupport C)
  rwa [supportExtract_of_subset C hC _ (Finset.Subset.refl _)] at hh

theorem slot_plain_products {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i∈T,Prime (p i)) (I J C a : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (hprod : (∏ i∈T,p i)*I*J=C*a) :
    (∏ i∈T.filter (fun i => p i∈primeSupport C),p i)*
        supportExtract I (primeSupport C)*supportExtract J (primeSupport C)=C ∧
      (∏ i∈T.filter (fun i => p i∉primeSupport C),p i)*
        supportResidual I (primeSupport C)*supportResidual J (primeSupport C)=a := by
  have hp0 : (∏ i∈T,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i hi => (hp i hi).ne_zero)
  have hf := (prime_slot_allocation T p hp (primeSupport C)).1
  have hl := (prime_slot_allocation T p hp (primeSupport C)).2
  constructor
  · have he := extract_coprime_product C a hC ha hCa
    rw [← hprod,supportExtract_mul _ J (mul_ne_zero hp0 hI) hJ,
      supportExtract_mul _ I hp0 hI,hf] at he
    exact he
  · have he := residual_coprime_product C a hC ha hCa
    rw [← hprod,supportResidual_mul _ J (mul_ne_zero hp0 hI) hJ,
      supportResidual_mul _ I hp0 hI,hl] at he
    exact he

theorem centered_source_allocation {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (ν : ι → ℂ) (η : Character) (m A z : O) (t : ℝ)
    (I J C a : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hprod : (∏ i∈T,p i)*I*J=C*a)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∏ i∈T,ν i)*rowWeight η m A z t ((∏ i∈T,p i)*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      ((∏ i∈T.filter (fun i => p i∈primeSupport C),ν i)*rowWeight η m A z t C)*
        ((∏ i∈T.filter (fun i => p i∉primeSupport C),ν i)*rowWeight η m A z t a*
          idealRectangle W₁ W₂
            (X₁/Ideal.absNorm (supportExtract I (primeSupport C)))
            (X₂/Ideal.absNorm (supportExtract J (primeSupport C)))
            (Y₁/Ideal.absNorm (supportExtract I (primeSupport C)))
            (Y₂/Ideal.absNorm (supportExtract J (primeSupport C)))
            (supportResidual I (primeSupport C)) (supportResidual J (primeSupport C))) := by
  have hrect := idealRectangle_extract W₁ W₂ X₁ X₂ Y₁ Y₂
    (supportExtract I (primeSupport C)) (supportExtract J (primeSupport C))
    (supportResidual I (primeSupport C)) (supportResidual J (primeSupport C))
  rw [support_reconstruct I hI,support_reconstruct J hJ] at hrect
  rw [hprod,map_mul,hrect,← Finset.prod_filter_mul_prod_filter_not T (fun i => p i∈primeSupport C) ν]
  ring

end SevenEighths.CenteredMomentCommonAllocation

end

end OAI
