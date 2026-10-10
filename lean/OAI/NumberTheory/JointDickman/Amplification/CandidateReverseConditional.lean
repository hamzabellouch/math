import OAI.NumberTheory.JointDickman.Amplification.CandidateReverseMajorant

namespace OAI

/-! # A uniform conditional mean for the actual forward candidate entry -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- The other endpoint types may be completely arbitrary. Averaging just
the lower endpoint gives the manuscript's uniform bound. -/
theorem latentCandidateKernel_reverse_conditional_mean
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ),
      (∀ e, χ e ≤ 1) → ∀ i k : Fin M, i < k → S k ⊆ auxiliaryPrimes B →
      finiteExpectation (independentPrimeSetMass B)
        (fun R => latentCandidateKernel B L T H M τ C (Function.update S i R.val) χ i k) ≤
          K/(T : ℝ)*singularFactor 24 (k.val-i.val) := by
  classical
  obtain ⟨K,hK,hbound⟩ := reverseEndpointRowEnvelope_mean_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hbound hB
  intro L T H M τ C hT hTs S χ hχ i k hik hSk
  have hik' : k ≠ i := (ne_of_lt hik).symm
  have hi : i.val < k.val := hik
  calc
    _ ≤ finiteExpectation (independentPrimeSetMass B)
        (fun R => reverseEndpointRowEnvelope B L T (k.val-i.val) τ C (S k) R.val) := by
      apply finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
      intro R
      simpa only [Function.update_of_ne hik',Function.update_self] using
        latentCandidateKernel_le_reverseRowEnvelope (L := L) (H := H) (τ := τ) (C := C) (Function.update S i R.val) χ hB hT hTs hχ i k hik
    _ ≤ _ := hbound L T _ τ C hT hTs (by omega) (S k) hSk


end JointDickman

end OAI
