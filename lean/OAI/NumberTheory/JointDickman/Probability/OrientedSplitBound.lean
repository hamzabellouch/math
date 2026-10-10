import OAI.NumberTheory.JointDickman.Arithmetic.AmplificationPrimeRanges

namespace OAI

/-! # One oriented change interval in the actual conditional split law -/

namespace JointDickman

open Finset Filter
open scoped Topology

open Classical in
noncomputable def additionRatioTest (Y T a c : ℝ) (U V : Finset ℕ) : ℝ :=
  if T * (c * (∏ p ∈ V, p : ℕ)) ≤ a * (∏ p ∈ U, p : ℕ) ∧
      a * (∏ p ∈ U, p : ℕ) ≤ 2 * (T * (c * (∏ p ∈ V, p : ℕ))) ∧
      Y / 2 ≤ Real.log (∏ p ∈ U, p : ℕ) then 1 else 0

noncomputable def orientedSplitMass (B : ℕ) (A D : Finset ℕ) (Y C T : ℝ) : ℝ :=
  let P := additionPrimes B Y
  let Q := upperAdditionPrimes B Y
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
  keptHighAverage (A ∩ P) (A ∩ Q) (fun I =>
    keptHighAverage (D ∩ P) (D ∩ Q) (fun J =>
      noHighAdditionAverage P Q (remainingPrimeParameter D) k (fun V =>
        noHighAdditionAverage P Q (remainingPrimeParameter A) k (fun U =>
          additionRatioTest Y T (∏ p ∈ I ∪ (A ∩ Q), p : ℕ)
            (∏ p ∈ J ∪ (D ∩ Q), p : ℕ) U V))))

theorem additionRatioTest_average (B : ℕ) (A D : Finset ℕ) (Y T a c : ℝ) :
    subsetAverage (additionPrimes B Y) (conditionalAdditionParameter D) (fun V =>
      subsetAverage (additionPrimes B Y) (conditionalAdditionParameter A)
        (fun U => additionRatioTest Y T a c U V)) = firstAdditionRatioMass B A D Y T a c := by
  classical
  unfold subsetAverage firstAdditionRatioMass additionRatioTest
  apply sum_congr rfl
  intro V _
  congr 1
  apply sum_congr rfl
  intro U _
  simp only [mul_ite, mul_one, mul_zero]

/-- The no-high-change probability and the low ratio probability multiply
in the exact conditional law. This statement retains the actual high masses. -/
theorem oriented_split_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (A D : Finset ℕ) (Y C T : ℝ),
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      0 < Y → Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B → 0 < T →
      orientedSplitMass B A D Y C T ≤
        (1 / 2 : ℝ)^(A ∩ upperAdditionPrimes B Y).card *
        (1 / 2 : ℝ)^(D ∩ upperAdditionPrimes B Y).card *
        (highNoAdditionMass (upperAdditionPrimes B Y) (remainingPrimeParameter D)
          ((2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C) *
        highNoAdditionMass (upperAdditionPrimes B Y) (remainingPrimeParameter A)
          ((2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C) * (K / Y)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := first_addition_ratio_bound hFord hM κ
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with B hb
  intro A D Y C T hA hD hsize hY0 hY hYB hT
  let P := additionPrimes B Y
  let Q := upperAdditionPrimes B Y
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
  have hd : Disjoint P Q := additionPrimeRanges_disjoint B Y
  have hQA : ∀ p ∈ Q, 0 ≤ remainingPrimeParameter A p ∧ remainingPrimeParameter A p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc A (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  have hQD : ∀ p ∈ Q, 0 ≤ remainingPrimeParameter D p ∧ remainingPrimeParameter D p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc D (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  have hnonneg : 0 ≤ highNoAdditionMass Q (remainingPrimeParameter D) k *
      highNoAdditionMass Q (remainingPrimeParameter A) k :=
    mul_nonneg (highNoAdditionMass_nonneg Q _ k hQD) (highNoAdditionMass_nonneg Q _ k hQA)
  unfold orientedSplitMass
  apply keptHighAverage_pair_bound _ _ _ _ (hd.mono inter_subset_right inter_subset_right)
    (hd.mono inter_subset_right inter_subset_right)
  intro I hI J hJ
  have hIaux : I ∪ (A ∩ Q) ⊆ auxiliaryPrimes B :=
    union_subset (fun p hp => hA (mem_inter.mp (hI hp)).1) (fun p hp => hA (mem_inter.mp hp).1)
  have hJaux : J ∪ (D ∩ Q) ⊆ auxiliaryPrimes B :=
    union_subset (fun p hp => hD (mem_inter.mp (hJ hp)).1) (fun p hp => hD (mem_inter.mp hp).1)
  have ha : (0 : ℝ) < (∏ p ∈ I ∪ (A ∩ Q), p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hIaux hp)).pos)
  have hc : (0 : ℝ) < (∏ p ∈ J ∪ (D ∩ Q), p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hJaux hp)).pos)
  rw [noHighAdditionAverage_pair_eq P Q hd]
  change highNoAdditionMass Q (remainingPrimeParameter D) k *
      highNoAdditionMass Q (remainingPrimeParameter A) k *
        subsetAverage P (conditionalAdditionParameter D) (fun V =>
          subsetAverage P (conditionalAdditionParameter A) (fun U =>
            additionRatioTest Y T (∏ p ∈ I ∪ (A ∩ Q), p : ℕ)
              (∏ p ∈ J ∪ (D ∩ Q), p : ℕ) U V)) ≤ _
  rw [additionRatioTest_average]
  exact mul_le_mul_of_nonneg_left
    (hb A D Y T _ _ hA hsize hY hYB hT ha hc) hnonneg

end JointDickman

end OAI
