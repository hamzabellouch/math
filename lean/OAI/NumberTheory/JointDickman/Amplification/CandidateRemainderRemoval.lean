import OAI.NumberTheory.JointDickman.Amplification.CandidateMeanBridge

namespace OAI

/-! # Remainder regularity removal for the actual candidate weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem candidate_remainder_removal
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → ∀ j T U V : ℕ,
          0 < T → Real.log T ≤ (B : ℝ)/10 → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          ∀ g h : Finset ℕ → ℝ, (∀ S, |g S| ≤ 1) → (∀ R, |h R| ≤ 1) →
          |subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
              (candidateRetainedWeight B L j τ C T V))-
            subsetKernelBilinear B g h (regularRemainderKernel B L τ C
              (candidateRetainedWeight B L j τ C T V))| ≤
          K*(ε B+Real.exp (-(1/10 : ℝ)*C))*
            amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1) := by
  obtain ⟨K,hK,hloss⟩ := remainderKernel_regularity_estimate hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss,eventually_ge_atTop 30] with B hb hB
  intro C hC j T U V hT hlog hU g h hg hh
  have he := hb C hC (candidateRetainedWeight B L j τ C T V)
    (fun A _ D _ => (candidateRetainedWeight_bounds B L j τ C T V A D).1)
    (fun A _ D _ hne => candidateRetainedWeight_support hB hT hlog hne) g h hg hh
  exact he.trans (mul_le_mul_of_nonneg_left
    (candidateRetainedWeight_positive_mass_le B L j T U V τ C hU)
    (mul_nonneg hK.le (add_nonneg (hε0 B) (Real.exp_pos _).le)))

end JointDickman

end OAI
