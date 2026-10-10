import OAI.NumberTheory.JointDickman.Amplification.CandidateRowMajorant

namespace OAI

/-! # A uniform conditional mean for the actual forward candidate entry -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- The other endpoint types may be completely arbitrary. Averaging just
the upper endpoint gives the manuscript's uniform bound. -/
theorem latentCandidateKernel_forward_conditional_mean
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ),
      (∀ e, χ e ≤ 1) → ∀ i k : Fin M, i < k → S i ⊆ auxiliaryPrimes B →
      finiteExpectation (independentPrimeSetMass B)
        (fun R => latentCandidateKernel B L T H M τ C (Function.update S k R.val) χ i k) ≤
          K/(T : ℝ)*singularFactor 24 (k.val-i.val) := by
  classical
  obtain ⟨K,hK,hbound⟩ := endpointRowEnvelope_mean_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hbound hB
  intro L T H M τ C hT hTs S χ hχ i k hik hSi
  have hik' : i ≠ k := ne_of_lt hik
  have hi : i.val < k.val := hik
  calc
    _ ≤ finiteExpectation (independentPrimeSetMass B)
        (fun R => endpointRowEnvelope B L T (k.val-i.val) τ C (S i) R.val) := by
      apply finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
      intro R
      simpa only [Function.update_of_ne hik',Function.update_self] using
        latentCandidateKernel_le_rowEnvelope (L := L) (H := H) (τ := τ) (C := C) (Function.update S k R.val) χ hB hT hTs hχ i k hik
    _ ≤ _ := hbound L T _ τ C hT hTs (by omega) (S i) hSi

/-- The same estimate integrated over the independent endpoint law. -/
theorem latentCandidateKernel_forward_mean
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, χ e ≤ 1) → ∀ i k : Fin M, i < k →
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k) ≤
          K/(T : ℝ)*singularFactor 24 (k.val-i.val) := by
  classical
  obtain ⟨K,hK,hbound⟩ := endpointRowEnvelope_mean_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hbound hB
  intro L T H M τ C hT hTs χ hχ i k hik
  have hj : k.val-i.val ≠ 0 := by have hi : i.val < k.val := hik; omega
  calc
    _ ≤ finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => endpointRowEnvelope B L T (k.val-i.val) τ C (S i).val (S k).val) := by
      apply finiteExpectation_mono _
        (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B))
      intro S
      exact latentCandidateKernel_le_rowEnvelope (fun i => (S i).val) χ hB hT hTs hχ i k hik
    _ = finiteExpectation (independentPrimeSetMass B) (fun S =>
        finiteExpectation (independentPrimeSetMass B)
          (fun R => endpointRowEnvelope B L T (k.val-i.val) τ C S.val R.val)) :=
      siteProduct_expectation_two (fun _ : Fin M => independentPrimeSetMass B)
        (fun _ => independentPrimeSetMass_sum B) (ne_of_lt hik)
        (fun S R : (auxiliaryPrimes B).powerset =>
          endpointRowEnvelope B L T (k.val-i.val) τ C S.val R.val)
    _ ≤ finiteExpectation (independentPrimeSetMass B)
        (fun _ => K/(T : ℝ)*singularFactor 24 (k.val-i.val)) := by
      apply finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
      intro S
      exact hbound L T _ τ C hT hTs hj S.val (mem_powerset.mp S.property)
    _ = _ := finiteExpectation_const _ (independentPrimeSetMass_sum B) _

end JointDickman

end OAI
