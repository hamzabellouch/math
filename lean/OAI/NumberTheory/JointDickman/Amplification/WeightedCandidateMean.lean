import OAI.NumberTheory.JointDickman.Amplification.WeightedCandidateComparison

namespace OAI

/-! # The actual smooth latent candidate mean compared with its arithmetic sum -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weightedCandidateMean_eq_remainderMean {B L T H M V : ℕ} {τ C : ℝ}
    (hB : 1 < B) (hT : 0 < T) (hV : ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V)
    (i t : Fin M) (hit : i < t) (hH : H < t.val-i.val) (hjT : t.val-i.val < T)
    (q : ℕ → ℕ → ℝ) (g h : Finset ℕ → ℝ) :
    subsetKernelBilinear B g h
      (candidateSiteKernel B L T H M τ C
        (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
          q (candidateHigh e) (candidateLow e)) i t) =
    independentRootMean B L τ C*subsetKernelBilinear B g h
      (regularRemainderKernel B L τ C (weightedCandidateRetained B L (t.val-i.val) τ C T V q)) := by
  unfold subsetKernelBilinear
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro R hR
  rw [candidateSiteKernel_product_weight hB hT hV i t hit hH hjT q
    (mem_powerset.mp hS) (mem_powerset.mp hR)]
  ring

open Classical in
theorem weighted_candidate_arithmetic_comparison
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ Kr Kc : ℝ, 0 < Kr ∧ 0 < Kc ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ er ec : ℕ → ℝ, (∀ B, 0 ≤ er B) ∧ (∀ B, 0 ≤ ec B) ∧
        Tendsto er atTop (𝓝 0) ∧ Tendsto ec atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V : ℕ),
          0 ≤ C → 0 < T → Real.log T ≤ (B : ℝ)/10 →
          (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ i t : Fin M, i < t → H < t.val-i.val → t.val-i.val < T →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, 0 ≤ q a b ∧ q a b ≤ 1) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
              (subsetSiteTest (auxiliaryPrimes B) h)
              (candidateSiteKernel B L T H M τ C
                (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
          q (candidateHigh e) (candidateLow e)) i t)-
            independentRootMean B L τ C*weightedAmplificationArithmeticSum B (t.val-i.val) T U V q h g| ≤
          independentRootMean B L τ C*
            (Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B (t.val-i.val) T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 (t.val-i.val)*(ec B+Real.exp (-(1/10 : ℝ)*C))) := by
  obtain ⟨Kr,hKr,hrem⟩ := weighted_candidate_remainder_removal hM
  obtain ⟨Kc,hKc,hcoef⟩ := weighted_candidate_coefficient_removal hFord hM
  refine ⟨Kr,Kc,hKr,hKc,?_⟩
  intro L τ hL hτ
  obtain ⟨er,her0,her,hrem⟩ := hrem L τ hL hτ
  obtain ⟨ec,hec0,hec,hcoef⟩ := hcoef L τ hL hτ
  refine ⟨er,ec,her0,hec0,her,hec,?_⟩
  filter_upwards [hrem,hcoef,eventually_ge_atTop 30] with B hr hc hB
  intro C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT q hq g h hg hh
  have hB1 : 1 < B := by omega
  have hj : 0 < t.val-i.val := Nat.sub_pos_of_lt hit
  have her := hr C hC (t.val-i.val) T U V hT hlog hU
    q hq (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
    (fun S => hg _) (fun R => hh _)
  have hec := hc T hT hlog C (t.val-i.val) U V hC hj hU hdyU hdyV q (fun a b => by rw [abs_of_nonneg (hq a b).1]; exact (hq a b).2) g h hg hh
  rw [weightedCandidateMean_eq_remainderMean hB1 hT hV i t hit hH hjT q]
  rw [← mul_sub,abs_mul,abs_of_nonneg (independentRootMean_nonneg B L τ C)]
  apply mul_le_mul_of_nonneg_left _ (independentRootMean_nonneg B L τ C)
  have hs := abs_sub_le
    (subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h)
      (regularRemainderKernel B L τ C (weightedCandidateRetained B L (t.val-i.val) τ C T V q)))
    (subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
      (subsetSiteTest (auxiliaryPrimes B) h)
      (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L (t.val-i.val) τ C T V q)))
    (weightedAmplificationArithmeticSum B (t.val-i.val) T U V q h g)
  rw [abs_sub_comm] at her
  exact hs.trans (by linarith only [her,hec])

end JointDickman

end OAI
