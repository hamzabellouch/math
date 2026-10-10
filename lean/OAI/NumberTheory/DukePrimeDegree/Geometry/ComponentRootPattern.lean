import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelStabilizerMeasurable
import OAI.NumberTheory.DukePrimeDegree.Geometry.MeasureConjugation

namespace OAI

/-!
# The measurable root pattern of actual ergodic components

A split diagonal rescales each real root group by a nonzero scalar.
Thus it preserves the predicate that the whole root group fixes a
measure, even when it moves that measure. For the normalizer-covariant
component kernel this gives an invariant measurable event on the
component base; it does not assert that individual components are fixed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootInvarianceRelation_iff_full_root {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n)) :
    rootInvarianceRelation μ i j ↔ ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
  constructor
  · rintro (he | ⟨_, hroot⟩)
    · exact (hij he).elim
    · exact hroot
  · exact fun hroot => Or.inr ⟨hij, hroot⟩

lemma all_root_mem_map_diagonal_iff {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n))
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    (∀ s : ℝ, Matrix.SpecialLinearGroup.transvection hij s ∈
      invariantRightSubgroup (μ.map (fun x => rightAction x
        (diagonalOneParameter ell hell t)))) ↔
      ∀ s : ℝ, Matrix.SpecialLinearGroup.transvection hij s ∈ invariantRightSubgroup μ := by
  let a := diagonalOneParameter ell hell t
  let c := Real.exp ((ell i - ell j) * t)
  have hc : c ≠ 0 := Real.exp_ne_zero _
  have hconj (s : ℝ) : a * Matrix.SpecialLinearGroup.transvection hij s * a⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (c * s) := by
    rw [← diagonalOneParameter_neg]
    exact diagonal_conjugation_transvection ell hell hij s t
  constructor
  · intro h s
    have hs := (mem_invariantRightSubgroup_map_iff μ a _).mp (h (s / c))
    rw [hconj, mul_div_cancel₀ _ hc] at hs
    exact hs
  · intro h s
    apply (mem_invariantRightSubgroup_map_iff μ a _).mpr
    rw [hconj]
    exact h _

lemma rootInvarianceRelation_map_diagonal_iff {n : ℕ}
    (μ : Measure (X n)) (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0)
    (t : ℝ) (i j : Fin n) :
    rootInvarianceRelation (μ.map (fun x => rightAction x
      (diagonalOneParameter ell hell t))) i j ↔ rootInvarianceRelation μ i j := by
  by_cases hij : i = j
  · simp only [rootInvarianceRelation, hij, true_or]
  · rw [rootInvarianceRelation_iff_full_root hij,
      rootInvarianceRelation_iff_full_root hij]
    exact all_root_mem_map_diagonal_iff hij μ ell hell t

lemma measurableSet_kernel_rootInvarianceRelation
    {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (κ : Kernel Z (X n)) [IsFiniteKernel κ] (i j : Fin n) :
    MeasurableSet {z | rootInvarianceRelation (κ z) i j} := by
  by_cases hij : i = j
  · simp only [rootInvarianceRelation, hij, true_or, ofPred_true]
    exact MeasurableSet.univ
  · have he : {z | rootInvarianceRelation (κ z) i j} =
        {z | ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
          invariantRightSubgroup (κ z)} := by
      ext z
      exact rootInvarianceRelation_iff_full_root hij (κ z)
    rw [he]
    exact measurableSet_kernel_root_invariant hij κ

/-- The actual component root pattern is unchanged along the specified
diagonal's action on the component base, almost everywhere. -/
theorem ae_component_root_pattern_diagonal {n : ℕ}
    (H : Subgroup (G n)) (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ)
    (ha : diagonalOneParameter ell hell t ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ)
    (i j : Fin n) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      rootInvarianceRelation
        (condExpKernel μ (actionInvariantSigma H (X n))
          (rightAction z (diagonalOneParameter ell hell t))) i j ↔
      rootInvarianceRelation (condExpKernel μ (actionInvariantSigma H (X n)) z) i j := by
  filter_upwards [lattice_normalizer_component_covariance H
    (diagonalOneParameter ell hell t) ha μ hμ] with z hz
  rw [← hz]
  exact rootInvarianceRelation_map_diagonal_iff _ ell hell t i j

end DukePrimeDegree

end

end OAI
