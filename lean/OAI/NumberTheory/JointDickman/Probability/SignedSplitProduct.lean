import OAI.NumberTheory.JointDickman.Amplification.SubsetThinning
import OAI.NumberTheory.JointDickman.Counting.CoefficientDomination

namespace OAI

/-! # The signed fair-split product law used by the kernel -/

namespace JointDickman
open Finset

open Classical in
noncomputable def splitProductMass (P S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ A ∈ P.powerset, subsetRetentionMass S A*(if (∏ p ∈ A, p) = n then 1 else 0)

noncomputable def signedSplitProductMass (P : Finset ℕ) (g : Finset ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S *
    splitProductMass P S n

theorem splitProductMass_nonneg (P S : Finset ℕ) (n : ℕ) :
    0 ≤ splitProductMass P S n := by
  classical
  apply sum_nonneg
  intro A _
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem signedSplitProductMass_one (P : Finset ℕ) (n : ℕ) :
    signedSplitProductMass P (fun _ => 1) n = primeProductMass P (1/2) n := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp only [mul_one]
  rw [subsetRetentionMass_expectation]
  unfold primeProductMass
  apply sum_congr rfl
  intro A _
  have hq : (fun p : ℕ => (1/(p : ℝ))/2) = (fun p : ℕ => (1/2 : ℝ)/(p : ℝ)) := by
    funext p
    ring
  rw [hq]
  split_ifs <;> simp

theorem signedSplitProductMass_abs_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : Finset ℕ → ℝ} (hg : ∀ S ⊆ P, |g S| ≤ 1) (n : ℕ) :
    |signedSplitProductMass P g n| ≤ primeProductMass P (1/2) n := by
  classical
  rw [← signedSplitProductMass_one]
  unfold signedSplitProductMass
  calc
    _ ≤ ∑ S ∈ P.powerset,
        |bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S * splitProductMass P S n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      have hmass : 0 ≤ bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S := by
        apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
        exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
      rw [abs_mul,abs_mul,abs_of_nonneg hmass,abs_of_nonneg (splitProductMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg S (mem_powerset.mp hS)) hmass)
        (splitProductMass_nonneg _ _ _)

theorem signedSplitProductMass_coefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) →
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        C*coefficientWeight B n/((B : ℝ)*n) := by
  obtain ⟨C,hC,hbound⟩ := primeProductMass_coefficient_domination hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hboundB
  intro g hg n hn hsize
  exact (signedSplitProductMass_abs_le (auxiliaryPrimes_prime B) hg n).trans
    (hboundB n hn hsize)

end JointDickman

end OAI
