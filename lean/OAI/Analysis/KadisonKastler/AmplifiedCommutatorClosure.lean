import OAI.Analysis.KadisonKastler.CStarCommutatorClosure
import OAI.Analysis.KadisonKastler.PairedRepresentations

namespace OAI

/-! # Complete commutator estimates on finite represented closures -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteAmplifiedRepresentation (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarMatrix ι ι A →⋆ₐ[ℂ] (FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) :=
  hilbertMatrixHom.comp (coefficientMatrixMap π)

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_range (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (finiteAmplifiedRepresentation (ι := ι) π).range = matrixOperatorAlgebra π.range := by
  apply le_antisymm
  · rintro T ⟨X, rfl⟩
    refine ⟨coefficientMatrixMap π X, ?_, rfl⟩
    intro i j
    exact ⟨X i j, rfl⟩
  · rintro T ⟨Y, hY, rfl⟩
    have hex : ∀ i j, ∃ a : A, π a = Y i j := fun i j => hY i j
    choose X hX using hex
    refine ⟨CStarMatrix.ofMatrix X, ?_⟩
    change hilbertMatrix (coefficientMatrixMap π (CStarMatrix.ofMatrix X)) = hilbertMatrix Y
    congr 1
    apply CStarMatrix.ext
    intro i j
    exact hX i j

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix ι ι A) (x : FiniteHilbert ι H) (i : ι) :
    finiteAmplifiedRepresentation π X x i = ∑ j, π (X i j) (x j) := by
  change hilbertMatrix (coefficientMatrixMap π X) x i = _
  rw [hilbertMatrix_apply]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_commutator
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (X : CStarMatrix ι ι A) :
    diagonalOperator T * finiteAmplifiedRepresentation π X -
        finiteAmplifiedRepresentation π X * diagonalOperator T =
      hilbertMatrix (CStarMatrix.mapₗ
        ((innerDerivation T).comp π.toAlgHom.toLinearMap) X) := by
  ext x i
  simp only [sub_apply, mul_apply_eq_comp, WithLp.ofLp_sub, Pi.sub_apply,
    diagonalOperator_apply, finiteAmplifiedRepresentation_apply, hilbertMatrix_apply]
  change T (∑ j, π (X i j) (x j)) - (∑ j, π (X i j) (T (x j))) =
    ∑ j, (T (π (X i j) (x j)) - π (X i j) (T (x j)))
  rw [map_sum, Finset.sum_sub_distrib]

theorem completelyBounded_commutator_generated
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    (n : ℕ) (b : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H)
    (hb : b ∈ matrixVonNeumann (generatedVonNeumannAlgebra π.range)) (hbn : ‖b‖ ≤ 1) :
    ‖diagonalOperator T * b - b * diagonalOperator T‖ ≤ e := by
  apply commutator_bound_generated_contraction (finiteAmplifiedRepresentation π)
    (diagonalOperator T) he _ b _ hbn
  · intro X
    rw [finiteAmplifiedRepresentation_commutator, norm_hilbertMatrix]
    exact hcb n n X
  · rwa [finiteAmplifiedRepresentation_range, generated_matrixOperatorAlgebra]

end

end KadisonKastler

end OAI
