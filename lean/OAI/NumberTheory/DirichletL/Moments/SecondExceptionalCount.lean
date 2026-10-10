import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
import OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentSupport UniqueFactorizationMonoid
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

lemma supported_coprime_72 (C:Ideal O) (hC:Supported C) :
    IsCoprime (Ideal.span {(72:O)}) C := by
  let n:=primaryGenerator C
  have hn:Supported (Ideal.span {n}):=by rw [primary_span_supported C hC]; exact hC
  have h2:IsCoprime n (2:O):=(fixedBadMask_coprime n hn).of_mul_left_right.symm
  have h9: IsCoprime n (9:O):=
    (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n ((supported_span_iff n).mp hn).1).symm
  have h72:IsCoprime n (72:O):=by
    convert (h2.pow_right : IsCoprime n ((2:O)^3)).mul_right h9 using 1 ; norm_num
  rw [←primary_span_supported C hC,Ideal.isCoprime_span_singleton_iff]
  exact h72.symm

lemma common_prime_dvd_left (C D:Ideal O) (P:CommonIndex C D) : P.val∣C :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma common_prime_prime (C D:Ideal O) (hC:Supported C) (P:CommonIndex C D) :
    Prime (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma outer_nonzero_left (η:Character) (t:ℝ) (C D:Ideal O)
    (hne:heightCoeff η t C*star (heightCoeff η t D)≠0) : idealCoeff η C≠0 :=
  left_ne_zero_of_mul (left_ne_zero_of_mul hne)

theorem actual_canonical_exceptional_count (η:Character) (χ:RayFourExpansion.RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (Q:Ideal O) (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)})
    (hQC:IsCoprime Q C) (hη:idealCoeff η C≠0)
    (m:O) (hm:m≠0) (hmLam:goodLambda∣m) (hm2:(2:O)∣m)
    (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (hex:∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M:ℝ) (hZ:1<Z) (hCr:0≤Cr)
    (hN:∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) :
    (rows.card:ℝ)≤768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
        (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6) := by
  have he:elementCoeff η (primaryGenerator C)≠0 := by
    rw [←idealCoeff_span η (supported_primaryGenerator_ne_zero C hC),primary_span_supported C hC]
    exact hη
  have hinj:Function.Injective (fun P:CommonIndex C D=>Ideal.span {commonPrime C D P}):=by
    simpa only [commonPrime_span C D hC] using (Subtype.val_injective:Function.Injective (fun P:CommonIndex C D=>P.val))
  have hb:=actual_forcing_exceptional_count (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P hP
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),hQC.of_isCoprime_of_dvd_right (common_prime_dvd_left C D P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb

end SevenEighths.CenteredMomentSecondExceptionalCount

end

end OAI
