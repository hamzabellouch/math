import OAI.NumberTheory.JointDickman.Probability.RemainderKernel

namespace OAI

/-! # Published remainder-regularity estimate for bounded signed site tests -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def subsetKernelBilinear (B : ℕ) (g h : Finset ℕ → ℝ)
    (K : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*K S R

open Classical in
theorem remainderKernel_regularity_estimate
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ F : Finset ℕ → Finset ℕ → ℝ,
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            0 ≤ F A D) →
          (∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
            F A D ≠ 0 → (∏ p ∈ A,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
              (∏ p ∈ D,p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)) →
          ∀ g h : Finset ℕ → ℝ, (∀ S, |g S| ≤ 1) → (∀ R, |h R| ≤ 1) →
          |subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B) F)-
            subsetKernelBilinear B g h (regularRemainderKernel B L τ C F)| ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            (∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*F A D) := by
  obtain ⟨K,hK,hloss⟩ := weighted_remainder_failure hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss] with B hb
  intro C hC F hF hs g h hg hh
  calc
    _ ≤ ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        |F A D| *fairRemainingPairFailure B L τ C A D :=
      retentionKernel_remaining_error B L τ C F g h hg hh
    _ = ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        F A D*fairRemainingPairFailure B L τ C A D := by
      apply sum_congr rfl
      intro A hA
      apply sum_congr rfl
      intro D hD
      rw [abs_of_nonneg (hF A hA D hD)]
    _ ≤ _ := hb C hC F hF hs

end JointDickman

end OAI
