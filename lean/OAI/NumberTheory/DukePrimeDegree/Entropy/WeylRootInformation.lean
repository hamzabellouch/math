import OAI.NumberTheory.DukePrimeDegree.Geometry.WeylRootLeaves
import OAI.NumberTheory.DukePrimeDegree.Geometry.WeylDiagonalAction
import OAI.NumberTheory.DukePrimeDegree.Geometry.CanonicalRootBasic
import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalEntropy

namespace OAI

/-! # Actual root information and coefficients under coordinate permutations

The reindexed measure is the pushforward on the arithmetic quotient.  The
preceding box-level transport proves covariance of the normalized intrinsic
leaves, so their small-ball logarithms and integrated coefficients agree.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_rootInformation_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ s : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij s) = x → s = 0)
    (t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation (e.injective.ne hij) (μ.map (quotientReindex e)) t
      (quotientReindex e x) = rootInformation hij μ t x := by
  filter_upwards [ae_intrinsicRootLeaf_reindex e hij μ hfree] with x hx
  simp only [rootInformation, hx]

theorem rootInformationMean_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ s : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij s) = x → s = 0)
    (t : ℝ) :
    rootInformationMean (e.injective.ne hij) (μ.map (quotientReindex e)) t =
      rootInformationMean hij μ t := by
  unfold rootInformationMean
  exact (lintegral_map_equiv
    (fun x => ENNReal.ofReal (rootInformation (e.injective.ne hij)
      (μ.map (quotientReindex e)) t x))
    (quotientReindexHomeomorph e).toMeasurableEquiv).trans
      (lintegral_congr_ae ((ae_rootInformation_reindex e hij μ hfree t).mono
        (fun _ hx => congrArg ENNReal.ofReal hx)))

/-- No entropy formula is used to permute the actual canonical root
coefficients; this follows by transporting their defining leaf integrals. -/
theorem canonicalRootCoefficient_reindex (d : ℕ) (e : Equiv.Perm (Fin (d + 1)))
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (i j : Fin (d + 1)) :
    canonicalRootCoefficient d (μ.map (quotientReindex e)) (e i) (e j) =
      canonicalRootCoefficient d μ i j := by
  by_cases hij : i = j
  · subst j
    rw [canonicalRootCoefficient_diagonal, canonicalRootCoefficient_diagonal]
  have hfree : ∀ᵐ x ∂μ, ∀ s : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij s) = x → s = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono (fun x hx => hx i j hij)
  simp only [canonicalRootCoefficient, dite_eq_right hij, dite_eq_right (e.injective.ne hij)]
  rw [rootInformationMean_reindex e hij μ hfree]

/-- The complete finite root-information form is unchanged when both
the measure and the diagonal weights are reindexed. -/
theorem rootEntropyForm_canonical_reindex (d : ℕ)
    (e : Equiv.Perm (Fin (d + 1))) (μ : Measure (X (d + 1)))
    [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d + 1) → ℝ) :
    rootEntropyForm (canonicalRootCoefficient d (μ.map (quotientReindex e)))
        (fun i => ell (e.symm i)) =
      rootEntropyForm (canonicalRootCoefficient d μ) ell := by
  have hc (i j : Fin (d + 1)) :
      canonicalRootCoefficient d (μ.map (quotientReindex e)) i j =
        canonicalRootCoefficient d μ (e.symm i) (e.symm j) := by
    simpa only [e.apply_symm_apply] using
      canonicalRootCoefficient_reindex d e μ hA (e.symm i) (e.symm j)
  unfold rootEntropyForm
  apply Fintype.sum_equiv e.symm _ _
  intro i
  apply Fintype.sum_equiv e.symm _ _
  intro j
  rw [hc]

end DukePrimeDegree

end

end OAI
