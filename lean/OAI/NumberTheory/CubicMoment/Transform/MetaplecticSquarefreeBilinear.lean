import OAI.NumberTheory.CubicMoment.Transform.MetaplecticWeightedBilinear

namespace OAI

/-! Automatic squarefree support for the actual bilinear Gauss sum.
No squarefree restriction is imposed on its original coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_bilinear_squarefree (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : Eisenstein → ℝ → ℂ) (V : ℝ)
    (hA : ∀ r ∈ A, primary r) (hB : ∀ u ∈ B, primary u) :
    (∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W r (norm u/V)) =
      ∑ r ∈ A.filter Squarefree, ∑ u ∈ B.filter Squarefree,
        α r*β u*gauss (r*u)*W r (norm u/V) := by
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hs : Squarefree r
  · rw [ite_eq_left hs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases ht : Squarefree u
    · rw [ite_eq_left ht]
    · rw [ite_eq_right ht,gauss_eq_zero_of_not_squarefree (primary_mul (hA r hr) (hB u hu))
        (fun h => ht (Squarefree.squarefree_of_dvd (dvd_mul_left u r) h))]
      ring
  · rw [ite_eq_right hs]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    rw [gauss_eq_zero_of_not_squarefree (primary_mul (hA r hr) (hB u hu))
      (fun h => hs (Squarefree.squarefree_of_dvd (dvd_mul_right r u) h))]
    ring

theorem UniformLogWeights.metaplectic_unrestricted_bilinear
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A B : Finset Eisenstein) (N Z V : ℝ),
      1 ≤ N → 1 ≤ Z → 0 < V →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ u ∈ B, primary u ∧ norm u ≤ Z) →
      ∀ α β : Eisenstein → ℂ,
      ‖∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W (w r) (norm u/V)‖^2 ≤
        K*(N*Z)^ε*(N+Z+(N*Z)^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2)*(∑ u ∈ B, ‖β u‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_weighted_bilinear hε
  refine ⟨K,hK,?_⟩
  intro w A B N Z V hN hZ hV hA hB α β
  rw [metaplectic_bilinear_squarefree A B α β (fun r => W (w r)) V
    (fun r hr => (hA r hr).1) (fun u hu => (hB u hu).1)]
  apply (hbound w (A.filter Squarefree) (B.filter Squarefree) N Z V hN hZ hV
    (fun r hr => ⟨(hA r (Finset.mem_filter.mp hr).1).1,(Finset.mem_filter.mp hr).2,
      (hA r (Finset.mem_filter.mp hr).1).2⟩)
    (fun u hu => ⟨(hB u (Finset.mem_filter.mp hu).1).1,(Finset.mem_filter.mp hu).2,
      (hB u (Finset.mem_filter.mp hu).1).2⟩) α β).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  · positivity
  · positivity

end CubicFirstMoment

end

end OAI
