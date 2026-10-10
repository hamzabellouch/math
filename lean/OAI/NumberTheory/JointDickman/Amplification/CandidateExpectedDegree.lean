import OAI.NumberTheory.JointDickman.Probability.CandidateSiteMean

namespace OAI

/-! # Uniform conditional degrees of the actual latent graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Every fixed endpoint type has bounded expected degree, including types
with no regular splitting. No division by a typical-event probability occurs. -/
theorem candidateSiteKernel_expected_degree
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, χ e ≤ 1) →
      ∀ i : Fin M, ∀ a ⊆ auxiliaryPrimes B,
      (∑ k : Fin M, finiteExpectation (independentPrimeSetMass B)
        (fun R => candidateSiteKernel B L T H M τ C χ i k a R.val)) ≤ K := by
  obtain ⟨K,hK,hbound⟩ := candidateSiteKernel_conditional_mean hFord hM
  refine ⟨2*K*Real.exp 24,by positivity,?_⟩
  filter_upwards [hbound] with B hbound
  intro L T H M τ C hT hTs χ hχ i a ha
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  calc
    _ ≤ ∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
        K/(T : ℝ)*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
      apply sum_le_sum
      intro k _
      by_cases hik : i = k
      · subst k
        simp only [candidateSiteKernel_diag,finiteExpectation,mul_zero,sum_const_zero,
          ne_eq,not_true_eq_false,false_and,ite_false,le_refl]
      · by_cases hfar : T ≤ Nat.dist i.val k.val
        · simp only [candidateSiteKernel_zero_of_far χ i k a _ hfar,finiteExpectation,
            mul_zero,sum_const_zero,not_lt.mpr hfar,and_false,ite_false,le_refl]
        · rw [ite_eq_left ⟨hik,Nat.lt_of_not_ge hfar⟩]
          exact hbound L T H M τ C hT hTs χ hχ i k hik a ha
    _ = K/(T : ℝ)*(∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
        singularFactor 24 (Nat.dist i.val k.val) else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp only [mul_zero]
    _ ≤ K/(T : ℝ)*(2*Real.exp 24*T) :=
      mul_le_mul_of_nonneg_left (distance_lag_singular_sum i T) (div_nonneg hK.le hTr.le)
    _ = _ := by field_simp

noncomputable def latentPrimeSiteKernel (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M)
    (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  candidateSiteKernel B L T H M τ C χ i k a.val b.val

theorem latentPrimeSiteKernel_realizes (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ)
    (S : Fin M → (auxiliaryPrimes B).powerset) (i k : Fin M) :
    realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C χ) S i k =
      latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k :=
  candidateSiteKernel_realizes B L T H M τ C χ (fun i => (S i).val) i k

theorem latentPrimeSiteKernel_row_mean
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ (i : Fin M) (a : (auxiliaryPrimes B).powerset),
      |siteRowMean (fun _ : Fin M => independentPrimeSetMass B)
        (latentPrimeSiteKernel B L T H M τ C χ) i a| ≤ K := by
  obtain ⟨K,hK,hbound⟩ := candidateSiteKernel_expected_degree hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hbound
  intro L T H M τ C hT hTs χ hχ i a
  have hnn : 0 ≤ siteRowMean (fun _ : Fin M => independentPrimeSetMass B)
      (latentPrimeSiteKernel B L T H M τ C χ) i a := by
    apply sum_nonneg
    intro j _
    apply finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    intro b
    exact candidateSiteKernel_nonneg _ _ _ _ _ _ _ χ (fun e => (hχ e).1) _ _ _ _
  rw [abs_of_nonneg hnn]
  have he : siteRowMean (fun _ : Fin M => independentPrimeSetMass B)
      (latentPrimeSiteKernel B L T H M τ C χ) i a =
      ∑ k : Fin M, finiteExpectation (independentPrimeSetMass B)
        (fun R => candidateSiteKernel B L T H M τ C χ i k a.val R.val) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
    simp only [candidateSiteKernel_diag,finiteExpectation,mul_zero,sum_const_zero,zero_add]
    rfl
  rw [he]
  exact hbound L T H M τ C hT hTs χ (fun e => (hχ e).2) i a.val (mem_powerset.mp a.property)

end JointDickman

end OAI
