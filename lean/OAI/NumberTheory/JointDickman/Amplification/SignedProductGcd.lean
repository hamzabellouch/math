import OAI.NumberTheory.JointDickman.Amplification.SignedPairPushforward
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductGcdError
import OAI.NumberTheory.JointDickman.Amplification.AmplificationWeightBound
import OAI.NumberTheory.JointDickman.Amplification.AmplificationMultiplier

namespace OAI

/-! # Coprimality removal for the actual signed product masses -/

namespace JointDickman
open Finset Filter

open Classical in
theorem primeProductMass_pair_sum_test (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (F : ℕ → ℕ → ℝ) :
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      primeProductMass P z a*primeProductMass P z b*F a b) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P (fun p => z/p) A*
          bernoulliSubsetMass P (fun p => z/p) D*F (∏ p ∈ A,p) (∏ p ∈ D,p) := by
  calc
    _ = ∑ a ∈ primeSplitProductSupport P, primeProductMass P z a*
        (∑ b ∈ primeSplitProductSupport P, primeProductMass P z b*F a b) := by
      simp_rw [mul_sum,mul_assoc]
    _ = ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) A*
        (∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) D*
          F (∏ p ∈ A,p) (∏ p ∈ D,p)) := by
      rw [primeProductMass_sum_test P hP]
      simp_rw [primeProductMass_sum_test P hP]
    _ = _ := by simp_rw [mul_sum,mul_assoc]

open Classical in
theorem halfPrimeProduct_bad_pair_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p) :
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      primeProductMass P (1/2) a*primeProductMass P (1/2) b*
        (if a.Coprime b then 0 else 1)) ≤ 1/(4*N : ℝ) := by
  rw [primeProductMass_pair_sum_test P hP]
  have he : (∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) A*
        bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) D*
          (if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then 0 else 1)) =
      finiteProbability (primeSubsetPairMass P (fun p => (1/2 : ℝ)/p) (fun p => (1/2 : ℝ)/p))
        (fun x => ¬(∏ p ∈ x.1.val,p).Coprime (∏ p ∈ x.2.val,p)) := by
    classical
    simp only [finiteProbability,primeSubsetPairMass,Fintype.sum_prod_type]
    have hout := sum_coe_sort P.powerset (fun A =>
      ∑ D : P.powerset, if ¬(∏ p ∈ A,p).Coprime (∏ p ∈ D.val,p) then
        bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) A*
          bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) D.val else 0)
    convert hout.symm using 1
    apply sum_congr rfl
    intro A _
    have hin := sum_coe_sort P.powerset (fun D =>
      if ¬(∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
        bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) A*
          bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) D else 0)
    rw [hin]
    apply sum_congr rfl
    intro D _
    by_cases h : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) <;> simp [h]
  rw [he]
  exact halfPrimeSubsetPair_gcd_error P hP hN hcut

open Classical in
theorem signedPrimeProductPair_coprime_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    (g h : (P → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (F : ℕ → ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ a b, |F a b| ≤ L) :
    |(∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      signedSplitProductMass P (subsetSiteTest P g) a*
        signedSplitProductMass P (subsetSiteTest P h) b*F a b)-
      (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        if a.Coprime b then signedSplitProductMass P (subsetSiteTest P g) a*
          signedSplitProductMass P (subsetSiteTest P h) b*F a b else 0)| ≤ L/(4*N : ℝ) := by
  let γ := signedSplitProductMass P (subsetSiteTest P g)
  let δ := signedSplitProductMass P (subsetSiteTest P h)
  let p := primeProductMass P (1/2)
  have hg' (a : ℕ) : |γ a| ≤ p a := signedSplitProductMass_abs_le hP (fun S _ => hg _) a
  have hh' (b : ℕ) : |δ b| ≤ p b := signedSplitProductMass_abs_le hP (fun S _ => hh _) b
  have hp (a : ℕ) : 0 ≤ p a := (abs_nonneg _).trans (hg' a)
  change |(∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P, γ a*δ b*F a b)-
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      if a.Coprime b then γ a*δ b*F a b else 0)| ≤ _
  have he : (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P, γ a*δ b*F a b)-
      (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        if a.Coprime b then γ a*δ b*F a b else 0) =
      ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        if a.Coprime b then 0 else γ a*δ b*F a b := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        |if a.Coprime b then 0 else γ a*δ b*F a b| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun a _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        p a*p b*L*(if a.Coprime b then 0 else 1) := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      by_cases hab : a.Coprime b
      · rw [ite_eq_left hab,ite_eq_left hab,abs_zero,mul_zero]
      · simp only [hab,ite_false,mul_one,abs_mul]
        exact mul_le_mul (mul_le_mul (hg' a) (hh' b) (abs_nonneg _) (hp a))
          (hF a b) (abs_nonneg _) (mul_nonneg (hp a) (hp b))
    _ = L*(∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        p a*p b*(if a.Coprime b then 0 else 1)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ L*(1/(4*N : ℝ)) := mul_le_mul_of_nonneg_left (halfPrimeProduct_bad_pair_mass P hP hN hcut) hL
    _ = _ := by ring

open Classical in
/-- The product weight sums the unique additive coefficient before the two
endpoint laws are pushed forward. -/
theorem amplificationFairKernel_product_expectation (B j : ℕ) (T : ℝ) (V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ x : auxiliaryPrimes B → Bool, ∑ z : auxiliaryPrimes B → Bool,
      fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) z*g x*h z*
        amplificationFairKernel B j T V x z) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
          signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
            amplificationProductWeight B j T V a b := by
  have hinner (x z : auxiliaryPrimes B → Bool) :
      (∑ y : auxiliaryPrimes B → Bool, ∑ w : auxiliaryPrimes B → Bool,
        fairRetentionMass x y*fairRetentionMass z w*
          amplificationProductWeight B j T V
            (retainedPrimeProduct (auxiliaryPrimes B) y)
            (retainedPrimeProduct (auxiliaryPrimes B) w)) =
      amplificationFairKernel B j T V x z := by
    unfold amplificationProductWeight amplificationFairKernel
    simp_rw [mul_sum]
    simp_rw [sum_comm (s := univ) (t := Ioc 0 V)]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro w _
    ring
  rw [signedSplitProductMass_pair_expectation (auxiliaryPrimes B) g h
    (amplificationProductWeight B j T V) _ _ (Subset.refl _) (Subset.refl _)]
  simp_rw [hinner]

open Classical in
/-- The actual smooth amplification weight satisfies the finite gcd-removal estimate. -/
theorem amplification_product_coprime_error {B j : ℕ} (hB : 0 < B) (hj : 0 < j)
    (T : ℝ) (V : ℕ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1) :
    |(∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        amplificationProductWeight B j T V a b)-
      (∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        if a.Coprime b then
          signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
          signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
            amplificationProductWeight B j T V a b else 0)| ≤
      ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ)) := by
  apply signedPrimeProductPair_coprime_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (show auxiliaryCutoff B ≠ 0 by exact pow_ne_zero _ (Nat.ne_of_gt hB))
    (fun p hp => by exact_mod_cast (mem_filter.mp hp).2) g h hg hh
    (amplificationProductWeight B j T V) (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg B))
  intro a b
  rw [abs_of_nonneg (amplificationProductWeight_bounds B hj T V a b).1]
  exact (amplificationProductWeight_bounds B hj T V a b).2


theorem amplification_gcd_rate_tendsto :
    Filter.Tendsto (fun B : ℕ => (amplificationMultiplier B : ℝ)*
      (((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))))
      Filter.atTop (nhds 0) := by
  have ht := ((tendsto_pow_atTop (by norm_num : (997 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun B : ℕ => (B : ℝ)^997) Filter.atTop Filter.atTop)
  have hlim : Filter.Tendsto (fun B : ℕ => (1/4 : ℝ)*((B : ℝ)^997)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp ht).const_mul (1/4 : ℝ)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun B => mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) _ hlim
  filter_upwards [coefficientScale_eventually_le,amplificationMultiplier_comparable,
    Filter.eventually_gt_atTop 1] with B hscale hmul hB
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hT : (amplificationMultiplier B : ℝ) ≤ B := hmul.2.2.trans (by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hBr.le (by norm_num : (8/25 : ℝ) ≤ 1)))
  calc
    _ ≤ (B : ℝ)*(((B : ℝ)*B)/(4*(auxiliaryCutoff B : ℝ))) := by
      apply mul_le_mul hT
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hB0.le)
          (by positivity)
      · exact div_nonneg (mul_nonneg hB0.le (coefficientScale_nonneg B)) (by positivity)
      · exact hB0.le
    _ = (1/4 : ℝ)*((B : ℝ)^997)⁻¹ := by
      simp only [auxiliaryCutoff,Nat.cast_pow]
      have hp : (B : ℝ)^1000 = (B : ℝ)^997*(B : ℝ)^3 := by rw [← pow_add]
      rw [hp]
      field_simp

end JointDickman

end OAI
