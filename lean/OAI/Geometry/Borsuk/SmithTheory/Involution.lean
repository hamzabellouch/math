import Mathlib

namespace OAI

namespace BorsukNine.SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}

noncomputable def involutionNorm (τ : ι ≃ ι) :
    (ι →₀ ZMod 2) →ₗ[ZMod 2] (ι →₀ ZMod 2) :=
  LinearMap.id + (Finsupp.domLCongr τ).toLinearMap

lemma involutionNorm_apply (τ : ι ≃ ι) (c : ι →₀ ZMod 2) (a : ι) :
    involutionNorm τ c a = c a + c (τ.symm a) := by
  simp [involutionNorm, Finsupp.domCongr, Finsupp.equivMapDomain_apply]

lemma involutionNorm_exact (τ : ι ≃ ι) (hτ : Function.Involutive τ)
    (hfree : ∀ a, τ a ≠ a) :
    LinearMap.ker (involutionNorm τ) ≤ LinearMap.range (involutionNorm τ) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  intro c hc
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  have heq (a : ι) : c (τ a) = c a := by
    have h := congrArg (fun b : ι →₀ ZMod 2 => b a) hc
    simp only [involutionNorm_apply, Finsupp.zero_apply, hsymm] at h
    have hh := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at hh
  refine ⟨c.filter (fun a => a < τ a), ?_⟩
  ext a
  rw [involutionNorm_apply, hsymm]
  simp only [Finsupp.filter_apply, ht]
  by_cases ha : a < τ a
  · simp [ha, not_lt_of_gt ha]
  · have hb : τ a < a := lt_of_le_of_ne (le_of_not_gt ha) (hfree a)
    simp [ha, hb, heq]

lemma involutionNorm_sq (τ : ι ≃ ι) (hτ : Function.Involutive τ) :
    (involutionNorm τ).comp (involutionNorm τ) = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro a
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  simp only [LinearMap.comp_apply, involutionNorm_apply, hsymm, ht,
    LinearMap.zero_apply, Finsupp.zero_apply]
  simp [add_comm, CharTwo.add_self_eq_zero]

end Involution

end BorsukNine.SmithTheory

end OAI
