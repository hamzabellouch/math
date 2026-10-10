import OAI.NumberTheory.JointDickman.Amplification.WeightedCandidateGcd
import OAI.NumberTheory.JointDickman.Probability.WeightedCandidateKernel
import OAI.NumberTheory.JointDickman.Amplification.CandidateRemainderRemoval

namespace OAI

/-! # Uniform removal errors with the actual bounded counting restriction -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedCandidateRetained_bounds (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (q : ℕ → ℕ → ℝ) (hq : ∀ a b, 0 ≤ q a b ∧ q a b ≤ 1) (A D : Finset ℕ) :
    0 ≤ weightedCandidateRetained B L j τ C T V q A D ∧
      weightedCandidateRetained B L j τ C T V q A D ≤ candidateRetainedWeight B L j τ C T V A D := by
  have hf := (candidateRetainedWeight_bounds B L j τ C T V A D).1
  exact ⟨mul_nonneg hf (hq _ _).1,
    (mul_le_mul_of_nonneg_left (hq _ _).2 hf).trans_eq (mul_one _)⟩

open Classical in
theorem weighted_candidate_remainder_removal
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ j T U V : ℕ,
          0 < T → Real.log T ≤ (B : ℝ)/10 → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, 0 ≤ q a b ∧ q a b ≤ 1) →
          ∀ g h : Finset ℕ → ℝ, (∀ S, |g S| ≤ 1) → (∀ R, |h R| ≤ 1) →
          |subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
              (weightedCandidateRetained B L j τ C T V q))-
            subsetKernelBilinear B g h (regularRemainderKernel B L τ C
              (weightedCandidateRetained B L j τ C T V q))| ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  obtain ⟨K,hK,hloss⟩ := remainderKernel_regularity_estimate hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss,eventually_ge_atTop 30] with B hb hB
  intro C hC j T U V hT hlog hU q hq g h hg hh
  have hbnd := weightedCandidateRetained_bounds B L j τ C T V q hq
  have he := hb C hC (weightedCandidateRetained B L j τ C T V q)
    (fun A _ D _ => (hbnd A D).1)
    (fun A _ D _ hne => candidateRetainedWeight_support hB hT hlog
      (left_ne_zero_of_mul hne)) g h hg hh
  have hmass : (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      weightedCandidateRetained B L j τ C T V q A D) ≤
      amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
    apply le_trans _ (candidateRetainedWeight_positive_mass_le B L j T U V τ C hU)
    apply sum_le_sum
    intro A hA
    apply sum_le_sum
    intro D hD
    have hp : ∀ p ∈ auxiliaryPrimes B, 0 ≤ (1/2 : ℝ)/p ∧ (1/2 : ℝ)/p ≤ 1 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
      exact ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩
    exact mul_le_mul_of_nonneg_left (hbnd A D).2
      (mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hA) hp)
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) hp))
  exact he.trans (mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hK.le (add_nonneg (hε0 B) (Real.exp_pos _).le)))

open Classical in
theorem weighted_candidate_coefficient_removal
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T → Real.log T ≤ (B : ℝ)/10 →
          ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → 0 < j → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, |q a b| ≤ 1) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
              (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q))-
            weightedAmplificationArithmeticSum B j T U V q h g| ≤
            ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hloss⟩ := amplification_signed_regularity_loss hFord hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss,eventually_gt_atTop 0] with B hb hB
  intro T hT hlog C j U V hC hj hU hdyU hdyV q hq g h hg hh
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hc := (weighted_amplification_regularization_error B L j τ C T U V q hq h g).trans
    (hb T hT1 hlog C j U V hC (Nat.ne_of_gt hj) hdyU hdyV h g hh hg)
  rw [abs_sub_comm] at hc
  exact (abs_sub_le _ (weightedRegularizedArithmeticSum B L j τ C T U V q h g) _).trans
    (add_le_add (weightedCandidateMean_coprime_error hB hj L T U V τ C hU q hq g h hg hh) hc)

end JointDickman

end OAI
