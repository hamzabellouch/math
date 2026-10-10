import OAI.NumberTheory.JointDickman.Amplification.ReverseEndpointTest
import OAI.NumberTheory.JointDickman.Amplification.EndpointRowEnvelope

namespace OAI

/-! # Conditional envelope for the lower endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def reverseEndpointRowEnvelope (B L T j : ℕ) (τ C : ℝ) (S R : Finset ℕ) : ℝ :=
  independentRootMean B L τ C/(B : ℝ)*
    ∑ A ∈ endpointSplits B L τ C S, endpointSplitWeight B L τ C S A*
      ∑ D ∈ endpointSplits B L τ C R, endpointSplitWeight B L τ C R D*
        reverseSupportedTest B T (∏ p ∈ A, p) j (∏ p ∈ D, p)

theorem reverseEndpointRowEnvelope_nonneg (B L T j : ℕ) (τ C : ℝ) (S R : Finset ℕ) :
    0 ≤ reverseEndpointRowEnvelope B L T j τ C S R := by
  apply mul_nonneg (div_nonneg (independentRootMean_nonneg _ _ _ _) (Nat.cast_nonneg B))
  apply sum_nonneg
  intro A _
  apply mul_nonneg (endpointSplitWeight_nonneg _ _ _ _ _ _) (sum_nonneg _)
  intro D _
  exact mul_nonneg (endpointSplitWeight_nonneg _ _ _ _ _ _)
    (reverseSupportedTest_nonneg _ _ _ _ _)

/-- The estimate is uniform in the fixed endpoint and in L, tau and C. -/
theorem reverseEndpointRowEnvelope_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T j : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      ∀ S ⊆ auxiliaryPrimes B,
      finiteExpectation (independentPrimeSetMass B)
        (fun R => reverseEndpointRowEnvelope B L T j τ C S R.val) ≤
          K/(T : ℝ)*singularFactor 24 j := by
  classical
  obtain ⟨D,hD,hsecond⟩ := reverseSupportedTest_mean_bound hFord hM
  obtain ⟨K,hK,hroot⟩ := independentRootMean_bounded hM
  refine ⟨K*D,by positivity,?_⟩
  filter_upwards [hsecond,hroot,eventually_gt_atTop 1] with B hsecond hroot hB
  intro L T j τ C hT hTs hj S hS
  have hm := independentRootMean_nonneg B L τ C
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hD0 : 0 ≤ D/(T : ℝ)*singularFactor 24 j :=
    mul_nonneg (div_nonneg hD.le (Nat.cast_nonneg T))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  have hfixed (A : Finset ℕ) (hA : A ∈ endpointSplits B L τ C S) :
      (∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        ∑ E ∈ endpointSplits B L τ C R, endpointSplitWeight B L τ C R E*
          reverseSupportedTest B T (∏ p ∈ A, p) j (∏ p ∈ E, p)) ≤
      D/(T : ℝ)*singularFactor 24 j := by
    have hAsub := (mem_endpointSplits.mp hA).1.trans hS
    have hr : Disjoint (∏ p ∈ A, p).primeFactors (Nat.primesLE (auxiliaryCutoff B)) := by
      rw [Nat.primeFactors_prod (fun p hp => auxiliaryPrimes_prime B p (hAsub hp))]
      exact auxiliarySubset_disjoint_small hAsub
    exact hsecond L T _ j τ C hT hTs hj hr
  have he : finiteExpectation (independentPrimeSetMass B)
      (fun R => reverseEndpointRowEnvelope B L T j τ C S R.val) =
      independentRootMean B L τ C/(B : ℝ)*
      ∑ A ∈ endpointSplits B L τ C S, endpointSplitWeight B L τ C S A*
        ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
          ∑ E ∈ endpointSplits B L τ C R, endpointSplitWeight B L τ C R E*
            reverseSupportedTest B T (∏ p ∈ A, p) j (∏ p ∈ E, p) := by
    unfold finiteExpectation independentPrimeSetMass
    change (∑ R : (auxiliaryPrimes B).powerset,
      (fun R : Finset ℕ => bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        reverseEndpointRowEnvelope B L T j τ C S R) R.val) = _
    calc
      _ = ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
            reverseEndpointRowEnvelope B L T j τ C S R := sum_coe_sort _ _
      _ = _ := by
        unfold reverseEndpointRowEnvelope
        simp_rw [mul_left_comm (bernoulliSubsetMass _ _ _) (independentRootMean _ _ _ _/(B : ℝ)),← mul_sum]
        congr 1
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro A _
        apply sum_congr rfl
        intro R _
        apply sum_congr rfl
        intro E _
        ring
  rw [he]
  calc
    _ ≤ independentRootMean B L τ C/(B : ℝ)*
        ∑ A ∈ endpointSplits B L τ C S, endpointSplitWeight B L τ C S A*
          (D/(T : ℝ)*singularFactor 24 j) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hm hBpos.le)
      exact sum_le_sum (fun A hA => mul_le_mul_of_nonneg_left (hfixed A hA)
        (endpointSplitWeight_nonneg _ _ _ _ _ _))
    _ = independentRootMean B L τ C/(B : ℝ)*
        ((∑ A ∈ endpointSplits B L τ C S, endpointSplitWeight B L τ C S A)*
          (D/(T : ℝ)*singularFactor 24 j)) := by rw [sum_mul]
    _ ≤ independentRootMean B L τ C/(B : ℝ)*
        ((B : ℝ)*(D/(T : ℝ)*singularFactor 24 j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (endpointSplitWeight_sum_le hB hS) hD0) (div_nonneg hm hBpos.le)
    _ = independentRootMean B L τ C*(D/(T : ℝ)*singularFactor 24 j) := by field_simp
    _ ≤ K*(D/(T : ℝ)*singularFactor 24 j) := mul_le_mul_of_nonneg_right (hroot L τ C) hD0
    _ = _ := by ring

end JointDickman

end OAI
