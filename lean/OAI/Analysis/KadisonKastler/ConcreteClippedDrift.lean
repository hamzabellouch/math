import OAI.Analysis.KadisonKastler.ClippedSequenceDrift
import OAI.Analysis.KadisonKastler.MatrixVonNeumann

namespace OAI

/-! # Clipped drift in the concrete matrix representation

This connects the support estimate for operator-valued matrices to the
bounded sequences in the represented tracial ultrapower. The norm bound
holds at each coordinate before the discarded tails are restored.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k : ℕ} {W : Type*} [Fintype W]

local instance concreteDriftSourceOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance concreteDriftSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance concreteDriftMatrixOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance concreteDriftMatrixStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _
local instance concreteDriftOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance concreteDriftOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance concreteDriftAmbientOrder :
    PartialOrder (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) := CStarAlgebra.spectralOrder _
local instance concreteDriftAmbientStarOrder :
    StarOrderedRing (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Recover the matrix of original-space operators from the concrete
amplified algebra. -/
def concreteMatrixEntries : Algebra (matrixVonNeumann (ι := Fin n) M) →⋆ₐ[ℂ]
    CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) :=
  (coefficientMatrixMap M.toStarSubalgebra.subtype).comp
    (matrixAlgebraEquiv (ι := Fin n) M).symm.toStarAlgHom

theorem hilbertMatrix_concreteMatrixEntries
    (a : Algebra (matrixVonNeumann (ι := Fin n) M)) :
    hilbertMatrix ((concreteMatrixEntries (M := M) (n := n)) a) = a.val :=
  matrixAlgebraEquiv_symm_operator M a

theorem concreteMatrixEntries_mem
    (a : Algebra (matrixVonNeumann (ι := Fin n) M)) (i j : Fin n) :
    (concreteMatrixEntries (M := M) (n := n)) a i j ∈ M :=
  ((matrixAlgebraEquiv (ι := Fin n) M).symm a i j).property

/-- The support and through-label estimates give the actual coordinate
clipped drift in the represented amplified factor. -/
theorem concrete_spectralClipped_drift_le
    (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (E : Generator.MatrixUnitSystem (Fin k) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra)
    (S : W → Finset (Fin n × Fin k)) (hS : ∀ w, (S w).card ≤ k)
    (K : W → Algebra (matrixVonNeumann (ι := Fin n) M))
    (hKsupport : ∀ w, (concreteMatrixEntries (M := M) (n := n)) (K w) =
      (concreteMatrixEntries (M := M) (n := n)) (K w) * supportProjection E (S w))
    (β : W → ℝ) (hβpos : ∀ w, 0 < β w)
    (hKcontract : ∀ z : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => (K w).val z)‖ ≤ ‖z‖)
    (hβ : ∀ a : Fin n × Fin k, (∑ w : W, if a ∈ S w then β w ^ 2 else 0) ≤ 64)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (z : Generator.FiniteHilbert (Fin n) H) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    ‖WithLp.toLp 2 (fun w =>
      (T * (spectralClip (β w) (K w)).val -
        (spectralClip (β w) (K w)).val * T) z)‖ ≤ 66 * δ * ‖z‖ := by
  have hcontract : ∀ y : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => hilbertMatrix ((concreteMatrixEntries (M := M) (n := n)) (K w)) y)‖ ≤ ‖y‖ := by
    simpa only [hilbertMatrix_concreteMatrixEntries] using hKcontract
  have ht := spectralClipped_matrixCommutator_drift_le_sixty_six M hPublished E hE S hS
    (fun w => (concreteMatrixEntries (M := M) (n := n)) (K w))
    (fun w i j => concreteMatrixEntries_mem (K w) i j) hKsupport
    β hβpos hcontract hβ h hδ hb z
  simp only [hilbertMatrix_matrixCommutator] at ht
  have hclip (w : W) : hilbertMatrix
      (clippedCoefficients (fun w => (concreteMatrixEntries (M := M) (n := n)) (K w)) β w) =
        (spectralClip (β w) (K w)).val := by
    change hilbertMatrix (spectralClip (β w) ((concreteMatrixEntries (M := M) (n := n)) (K w))) = _
    rw [← map_spectralClip (concreteMatrixEntries (M := M) (n := n)) (hβpos w),
      hilbertMatrix_concreteMatrixEntries]
  simpa only [hclip] using ht

end

end KadisonKastler

end OAI
