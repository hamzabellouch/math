import Mathlib

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma affine_sum_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : AffineSubspace ℝ V) (p : I → V) (hp : ∀ i, p i ∈ L)
    (w : I → ℝ) (hw : ∑ i, w i = 1) : ∑ i, w i • p i ∈ L := by
  rw [← Finset.affineCombination_eq_linear_combination univ p w hw]
  exact (affineSpan_le.mpr (Set.range_subset_iff.mpr hp))
    (affineCombination_mem_affineSpan hw p)

lemma affine_sum_apply {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (p : I → V)
    (w : I → ℝ) (hw : ∑ i, w i = 1) :
    f (∑ i, w i • p i) = ∑ i, w i • f (p i) := by
  rw [← Finset.affineCombination_eq_linear_combination univ p w hw,
    Finset.map_affineCombination _ _ _ hw f,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  rfl

end AffinePSD

end OAI
