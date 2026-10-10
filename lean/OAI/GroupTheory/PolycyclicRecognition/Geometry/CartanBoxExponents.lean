import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTransport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordBasisCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponents
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedBoxVolume

namespace OAI

/-! # Exact box exponents for the Cartan word model

The compact-template support equals the maximum of the determinant exponents
of the actual word boxes. This connects the Lie-algebra construction to the
Euclidean coordinate-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module MeasureTheory
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (e : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Support data in the fixed Euclidean coordinates on height. -/
def supportIn : SupportDatum W (Fin M.letterCount) M.Bases :=
  (M.supportDatum T hunimod).transport e

/-- The exponent of a word is the sum of the separately supported letters. -/
def boxCost (E : Set W) (w : M.wordList) : ℝ :=
  bracketWordExponent ((M.supportIn T hunimod e).weightSupport E) w

/-- The determinant exponent of each basis is its template support sum. -/
theorem columnBasisWeight_boxCost (E : Set W) (β : M.Bases) :
    columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).basisTemplateSupport E β := by
  unfold columnBasisWeight boxCost
  rw [sum_bracketWordExponent]
  rfl

/-- Maximizing the finite word-box determinant gives exactly `P(E)`. -/
theorem exists_maximizing_box_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) : ∃ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod e E) β.val ∧
      columnBasisWeight (M.boxCost T hunimod e E) β.val =
        (M.supportIn T hunimod e).templateSupport E := by
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod e E)
  refine ⟨β, hβ, le_antisymm ?_ ?_⟩
  · rw [M.columnBasisWeight_boxCost]
    exact (M.supportIn T hunimod e).basisTemplateSupport_le E β
  · apply (M.supportIn T hunimod e).templateSupport_le
    intro γ
    rw [← M.columnBasisWeight_boxCost T hunimod e E γ]
    exact hβ.2 γ.val (wordBasis_det_ne_zero M.letter M.wordList b₀ γ)

/-- Every maximizing basis has the same template exponent, including ties. -/
theorem columnBasisWeight_eq_templateSupport_of_maximizing
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod e E) β.val) :
    columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).templateSupport E := by
  obtain ⟨γ, _, hγ⟩ := M.exists_maximizing_box_basis T hunimod e b₀ E
  apply le_antisymm
  · rw [M.columnBasisWeight_boxCost]
    exact (M.supportIn T hunimod e).basisTemplateSupport_le E β
  · rw [← hγ]
    exact hβ.2 γ.val (wordBasis_det_ne_zero M.letter M.wordList b₀ γ)

/-- The volume of a maximizing coordinate box has precisely the template
support exponent, with its actual unscaled basis determinant. -/
theorem volume_maximizing_coordinateBox
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).templateSupport E) (r R : ℝ) :
    volume (weightedCoordinateBox (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod e E) β.val r R) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
      ENNReal.ofReal (Real.exp (r * (M.supportIn T hunimod e).templateSupport E)) *
      ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H) := by
  rw [volume_weightedCoordinateBox, hβ]

/-- Finiteness of the actual basis family gives positive uniform determinant
bounds, independent of every height template and scaling parameter. -/
theorem exists_uniform_wordBasis_determinant_bounds
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : M.Bases,
      c ≤ |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| ∧
      |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| ≤ C := by
  classical
  let d := fun β : M.Bases =>
    |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det|
  obtain ⟨βmin, _, hmin⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  obtain ⟨βmax, _, hmax⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hd (β : M.Bases) : 0 < d β :=
    abs_pos.mpr (wordBasis_det_ne_zero M.letter M.wordList b₀ β)
  exact ⟨d βmin, d βmax, hd βmin, hd βmax,
    fun β => ⟨hmin β (Finset.mem_univ β), hmax β (Finset.mem_univ β)⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
