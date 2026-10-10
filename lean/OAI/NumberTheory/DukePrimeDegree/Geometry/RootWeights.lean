import OAI.NumberTheory.DukePrimeDegree.Dynamics.PublishedEKL

namespace OAI

/-!
# Neutral diagonal directions for root leaves

Root leaves are unchanged along the kernel of their root character.
For two nonparallel roots, an explicit diagonal direction is neutral on
the first and expands the second. These are the directions used to
compare the root foliations in the entropy argument.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology Classical

namespace DukePrimeDegree

open PrimeDegreePackets

lemma rootCanonicalWeights_neutral (d : ℕ) {i j p : Fin (d + 1)}
    (hip : i ≠ p) (hjp : j ≠ p) :
    rootCanonicalWeights d p i = rootCanonicalWeights d p j := by
  simp [rootCanonicalWeights, coordinateContractionWeights, hip, hjp]

/-- Every root which is not equal or opposite to a fixed root is expanded
by a diagonal direction which centralizes the fixed root. -/
theorem exists_neutral_expanding_weights (d : ℕ)
    {i j k l : Fin (d + 1)} (_hij : i ≠ j) (hkl : k ≠ l)
    (hforward : ¬ (k = i ∧ l = j)) (hbackward : ¬ (k = j ∧ l = i)) :
    ∃ ell : Fin (d + 1) → ℝ,
      (∑ r, ell r) = 0 ∧ ell i = ell j ∧ ell l - ell k = 1 := by
  by_cases hli : l = i
  · have hki : k ≠ i := by simpa only [hli] using hkl
    have hkj : k ≠ j := by
      intro h
      exact hbackward ⟨h, hli⟩
    refine ⟨fun r => -rootCanonicalWeights d k r, ?_, ?_, ?_⟩
    · simp only [Finset.sum_neg_distrib, rootCanonicalWeights_sum, neg_zero]
    · exact congrArg Neg.neg (rootCanonicalWeights_neutral d hki.symm hkj.symm)
    · have h := rootCanonicalWeights_difference d hkl.symm
      linarith
  · by_cases hlj : l = j
    · have hki : k ≠ i := by
        intro h
        exact hforward ⟨h, hlj⟩
      have hkj : k ≠ j := by simpa only [hlj] using hkl
      refine ⟨fun r => -rootCanonicalWeights d k r, ?_, ?_, ?_⟩
      · simp only [Finset.sum_neg_distrib, rootCanonicalWeights_sum, neg_zero]
      · exact congrArg Neg.neg (rootCanonicalWeights_neutral d hki.symm hkj.symm)
      · have h := rootCanonicalWeights_difference d hkl.symm
        linarith
    · exact ⟨rootCanonicalWeights d l, rootCanonicalWeights_sum d l,
        rootCanonicalWeights_neutral d (Ne.symm hli) (Ne.symm hlj),
        rootCanonicalWeights_difference d hkl⟩

/-- A diagonal direction in the kernel of a root character fixes its
normalized intrinsic leaf measure almost everywhere. -/
theorem ae_rootLeaf_neutral_diagonal
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneutral : ell i = ell j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ
      (rightAction x (diagonalOneParameter ell hell t)) = intrinsicRootLeaf hij μ x := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hscale : (rootTimeScaling ell i j t : ℝ → ℝ) = id := by
    funext a
    simp [rootTimeScaling, hneutral]
  filter_upwards [ae_intrinsicRootLeaf_diagonal hij ell hell t μ hfree hinv,
    ae_intrinsicRootLeaf_spec hij μ hfree] with x hx hspec
  rw [hx]
  simp only [hscale, Measure.map_id, anchorNormalize, hspec.2, inv_one, one_smul]

end DukePrimeDegree

end OAI
