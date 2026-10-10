import OAI.NumberTheory.JointDickman.Amplification.RampedCandidate

namespace OAI

/-! # The counting-ramp candidate mean with all arithmetic removal errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem ramped_candidate_arithmetic_comparison
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
          ∀ δ σ : ℝ, 0 < δ →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
              (subsetSiteTest (auxiliaryPrimes B) h)
              (candidateSiteKernel B L T H M τ C
                (rampedCandidateCutoff B T δ σ) i t)-
            independentRootMean B L τ C*rampedAmplificationArithmeticSum B (t.val-i.val) T U V δ σ h g| ≤
          independentRootMean B L τ C*
            (Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B (t.val-i.val) T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 (t.val-i.val)*(ec B+Real.exp (-(1/10 : ℝ)*C))) := by
  obtain ⟨Kr,Kc,hKr,hKc,hcomp⟩ := weighted_candidate_arithmetic_comparison hFord hM
  refine ⟨Kr,Kc,hKr,hKc,?_⟩
  intro L τ hL hτ
  obtain ⟨er,ec,her0,hec0,her,hec,hcomp⟩ := hcomp L τ hL hτ
  refine ⟨er,ec,her0,hec0,her,hec,?_⟩
  filter_upwards [hcomp] with B hb
  intro C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT δ σ hδ g h hg hh
  let q := rampedProductCutoff T (t.val-i.val) δ σ
  have he := hb C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT
    q (rampedProductCutoff_bounds hδ T (t.val-i.val) σ) g h hg hh
  have hk : candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T δ σ) i t =
      candidateSiteKernel B L T H M τ C
        (fun e => candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e*
          q (candidateHigh e) (candidateLow e)) i t := by
    funext S R
    exact candidateSiteKernel_pair_cutoff_congr _ _ i t hit
      (rampedCandidateCutoff_pair B T δ σ i t) S R
  rw [← hk] at he
  have ha := rampedArithmetic_eq_weighted B (t.val-i.val) T U V (Nat.sub_pos_of_lt hit) δ σ h g
  rw [← ha] at he
  exact he

end JointDickman

end OAI
