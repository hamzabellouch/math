import OAI.NumberTheory.JointDickman.Amplification.SignedPairPushforward
import OAI.NumberTheory.JointDickman.Amplification.AmplificationDyadicIdentity

namespace OAI

/-! # The smooth amplification sum as the actual fair-split kernel -/

namespace JointDickman
open Finset

open Classical in
noncomputable def amplificationScalarWeight (B j : ℕ) (T : ℝ) (c b a : ℕ) : ℝ :=
  if a = b+j*c then coefficientWeight B c*
    (amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
      amplificationBump (b/(T*c))) else 0

open Classical in
noncomputable def amplificationFairKernel (B j : ℕ) (T : ℝ) (V : ℕ)
    (x z : auxiliaryPrimes B → Bool) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ y : auxiliaryPrimes B → Bool, ∑ w : auxiliaryPrimes B → Bool,
    fairRetentionMass x y*fairRetentionMass z w*
      amplificationScalarWeight B j T c
        (retainedPrimeProduct (auxiliaryPrimes B) w)
        (retainedPrimeProduct (auxiliaryPrimes B) y)

theorem primeSplitProductSupport_subset_Ioc {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {U : ℕ} (hU : (∏ p ∈ P, p) ≤ U) :
    primeSplitProductSupport P ⊆ Ioc 0 U := by
  classical
  intro n hn
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hn
  have hAP := mem_powerset.mp hA
  refine mem_Ioc.mpr ⟨prod_pos (fun p hp => (hP p (hAP hp)).pos),?_⟩
  exact (prod_le_prod_of_subset_of_one_le hAP (fun p hp _ => (hP p hp).one_le)).trans hU

open Classical in
theorem amplificationArithmeticTerm_factor (B j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    amplificationArithmeticTerm B j T g h c b a =
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        amplificationScalarWeight B j T c b a := by
  unfold amplificationArithmeticTerm amplificationScalarWeight
  split_ifs <;> ring

open Classical in
theorem amplificationArithmeticSum_eq_fairKernel (B j : ℕ) (T : ℝ) (U V : ℕ)
    (hU : (∏ p ∈ auxiliaryPrimes B, p) ≤ U)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    amplificationArithmeticSum B j T U V g h =
      ∑ x : auxiliaryPrimes B → Bool, ∑ z : auxiliaryPrimes B → Bool,
        fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) z*g x*h z*
          amplificationFairKernel B j T V x z := by
  have hsupport := primeSplitProductSupport_subset_Ioc (auxiliaryPrimes_prime B) hU
  unfold amplificationArithmeticSum
  simp_rw [amplificationArithmeticTerm_factor]
  have hpair (c : ℕ) := signedSplitProductMass_pair_expectation (auxiliaryPrimes B) g h
    (fun a b => amplificationScalarWeight B j T c b a) (Ioc 0 U) (Ioc 0 U) hsupport hsupport
  have hreplace (c : ℕ) :
      (∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
          amplificationScalarWeight B j T c b a) =
      ∑ x : auxiliaryPrimes B → Bool, ∑ z : auxiliaryPrimes B → Bool,
        fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) z*g x*h z*
          ∑ y : auxiliaryPrimes B → Bool, ∑ w : auxiliaryPrimes B → Bool,
            fairRetentionMass x y*fairRetentionMass z w*
              amplificationScalarWeight B j T c
                (retainedPrimeProduct (auxiliaryPrimes B) w)
                (retainedPrimeProduct (auxiliaryPrimes B) y) := by
    rw [sum_comm]
    exact hpair c
  simp_rw [hreplace]
  unfold amplificationFairKernel
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro w _
  ring

end JointDickman

end OAI
