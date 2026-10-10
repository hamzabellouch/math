import OAI.NumberTheory.DukePrimeDegree.Dynamics.ConjugationOrbit
import OAI.NumberTheory.PrimePackets.ObservationCovers

namespace OAI

/-!
# Matrix density for finite-volume lattice orbits

The actual lattice orbit quotient carries a nonzero finite invariant
measure. Conjugating any matrix which commutes with its stabilizer gives
a finite invariant matrix measure. Recurrence under a regular split
diagonal and the within-block root subgroups then forces the matrix into
the block-scalar algebra. No homogeneous classification is assumed here.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_diagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    slMatrixConjugation (diagonalOneParameter ell hell (-t)) =
      diagonalMatrixConjugation ell t := by
  funext M
  have hi : (diagonalOneParameter ell hell (-t))⁻¹ = diagonalOneParameter ell hell t := by
    rw [diagonalOneParameter_neg, inv_inv]
  unfold slMatrixConjugation
  rw [hi]
  change Matrix.diagonal (fun i => Real.exp (ell i * t)) * M *
      (diagonalOneParameter ell hell (-t)).val = _
  simp only [diagonalOneParameter, diagonalMatrixConjugation, mul_neg, neg_mul]

lemma slMatrixConjugation_root {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    slMatrixConjugation (Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ)) =
      rootMatrixConjugation i j 1 := by
  funext M
  simp only [slMatrixConjugation, Matrix.SpecialLinearGroup.transvection_inv,
    neg_neg, Matrix.SpecialLinearGroup.transvection_coe, rootMatrixConjugation,
    Matrix.transvection]

/-- The centralizer of the actual lattice stabilizer is contained in
the block-scalar algebra whenever the finite-volume orbit group contains
the split diagonal flow and the within-block roots. -/
theorem centralizer_subset_blockScalar_of_finite_orbit {n : ℕ}
    (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (hell : Function.Injective ell)
    (hdiag : ∀ t : ℝ, diagonalOneParameter ell hsum t ∈ H)
    (r : Setoid (Fin n))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val) :
    M ∈ blockScalarAlgebra r := by
  let F := conjugationOrbitMap g H M hM
  let ν := μ.map F
  have hF : Continuous F := continuous_conjugationOrbitMap g H M hM
  have hd : ∀ t : ℝ, ν.map (diagonalMatrixConjugation ell t) = ν := by
    intro t
    rw [← slMatrixConjugation_diagonal ell hsum t]
    exact conjugationOrbitMap_map_invariant g H M hM μ hinv
      ⟨diagonalOneParameter ell hsum (-t), hdiag (-t)⟩
  have hr : ∀ i j, i ≠ j → r i j → ν.map (rootMatrixConjugation i j 1) = ν := by
    intro i j hij hijr
    rw [← slMatrixConjugation_root i j hij]
    have hm : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ H := by
      simpa only [Matrix.SpecialLinearGroup.transvection_inv] using H.inv_mem (hroot i j hij hijr)
    exact conjugationOrbitMap_map_invariant g H M hM μ hinv
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hm⟩
  have hae : ∀ᵐ x ∂μ, F x ∈ blockScalarAlgebra r :=
    ae_of_ae_map hF.measurable.aemeasurable
      (ae_blockScalar_of_conjugation_invariance ν ell hell hd r hr)
  have hclosed : IsClosed (F ⁻¹' (blockScalarAlgebra r : Set (Matrix (Fin n) (Fin n) ℝ))) :=
    (blockScalarAlgebra r).toSubmodule.closed_of_finiteDimensional.preimage hF
  have hbase : (Quotient.mk _ (1 : H) : LatticeOrbitQuotient g H) ∈ μ.support := by
    rw [latticeOrbit_support_eq_univ g H μ hμ hinv]
    trivial
  have hmem := Measure.support_subset_of_isClosed hclosed hae hbase
  change conjugationOrbitMap g H M hM (Quotient.mk _ (1 : H)) ∈ blockScalarAlgebra r at hmem
  rw [conjugationOrbitMap_identity] at hmem
  exact hmem

end DukePrimeDegree

end

end OAI
