import OAI.Analysis.KadisonSimilarity.FreeProduct.EmbeddedWordStructure
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialWordActions
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialAutomorphismWords

namespace OAI

/-! The actual tracial free-product actions instantiate finite-stage word
classification. Both head covariance and matrix-unitary covariance follow
from the ordinary reduced-word formula. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
  [∀ s, Nonempty (I s)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)

/-- The matrix stage acts by actual ambient left multiplication. -/
def tracialMatrixLeftRepresentation (s : ℕ) : Matrix (I s) (I s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  G.left.comp (D.subtype.comp (M.embedding s))

variable (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ s, G.MatrixConjugationExtensionInput D (M.embedding s) A)

/-- The finite matrix group acts by its constructed free-product automorphisms. -/
def tracialMatrixUnitaryRepresentation (s : ℕ) :
    Matrix.unitaryGroup (I s) ℂ →* unitary (H →L[ℂ] H) :=
  G.matrixExtensionUnitaryRepresentation A D (M.embedding s) hgen hfaithful (hext s)

variable (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (I s) : ℝ)) Filter.atTop Filter.atTop)

/-- The finite matrix tower constructed from its actual tracial embeddings. -/
def baseTracialMatrixTower :=
  tracialMatrixTowerOfEmbeddings (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize

local instance tracialEmbeddedMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance
local instance tracialEmbeddedMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) := fun _ => inferInstance

variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)

include hword hτ in
/-- The left matrix covariance is the derived tracial head formula. -/
theorem tracialMatrixLeftRepresentation_inclusion (s : ℕ) (a : Matrix (I s) (I s) ℂ)
    (n : ℕ) :
    (G.tracialMatrixLeftRepresentation D M s a).comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (endpointHeadAction (n := n)
          (((G.baseTracialMatrixTower D M S hsize).stage s).left a))) := by
  exact hword.left_head hτ n (M.embedding s a)

include hword hτ in
omit [∀ s, Nonempty (I s)] in
/-- The unitary covariance is derived from the published algebraic extension
and the completed bounded-word identity. -/
theorem tracialMatrixUnitaryRepresentation_inclusion (s : ℕ)
    (u : Matrix.unitaryGroup (I s) ℂ) (n : ℕ) :
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (tracialMatrixWordAction (G.baseGeometry D).trace
          (G.baseGeometry D).vector (G.baseGeometry D).left (M.embedding s)
          (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
          (G.baseGeometry D).tracial
          (NestedTracialMatrices.denseRange_vector (G.baseGeometry D).trace
            (G.baseGeometry D).vector M) u n).toContinuousLinearMap) := by
  exact hword.matrix_extension_level (M.embedding s) u hgen hfaithful (hext s) hτ n

variable (Y : H →L[ℂ] H)
  (hYL : ∀ s a, Y.comp (G.tracialMatrixLeftRepresentation D M s a) =
    (G.tracialMatrixLeftRepresentation D M s a).comp Y)
  (hYU : ∀ s u, Y.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H) =
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp Y)

include S hsize hword hτ hYL hYU in
/-- Actual free-product symmetries force preservation of every word level. -/
theorem tracial_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) :=
  embedded_actions_word_levels_preserved (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize U
    (G.tracialMatrixLeftRepresentation D M)
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext)
    (G.tracialMatrixLeftRepresentation_inclusion A D M S hsize U hword hτ)
    (G.tracialMatrixUnitaryRepresentation_inclusion A D M hgen hfaithful hext U hword hτ)
    Y hYL hYU n

/-- The canonical multiplicity compression for the actual matrix tower. -/
def tracialWordRepeatedOperator (n : ℕ) :=
  wordLevelRepeatedOperator (G.baseTracialMatrixTower D M S hsize) U Y n

omit [IsClosed (A : Set P)] in
/-- The actual repeated coefficient is a contraction of the ambient operator. -/
theorem norm_tracialWordRepeatedOperator_le (n : ℕ) :
    ‖G.tracialWordRepeatedOperator A D M S hsize U Y n‖ ≤ ‖Y‖ :=
  norm_wordLevelRepeatedOperator_le (G.baseTracialMatrixTower D M S hsize) U Y n

omit [IsClosed (A : Set P)] in
/-- Its adjoint is the coefficient obtained from the ambient adjoint. -/
theorem tracialWordRepeatedOperator_adjoint (n : ℕ) :
    G.tracialWordRepeatedOperator A D M S hsize U Y.adjoint n =
      (G.tracialWordRepeatedOperator A D M S hsize U Y n).adjoint :=
  wordLevelRepeatedOperator_adjoint (G.baseTracialMatrixTower D M S hsize) U Y n

include hword hτ hYL hYU in
/-- Every repeated-letter word transforms by the canonical bounded
multiplicity operator; its action is independent of the repeated letter. -/
theorem tracial_repeated_word (n : ℕ) (a : WordMultiplicity (G.baseVector A 1) n)
    (d : G.baseSpace D) (r : centeredSubspace (G.baseVector D 1)) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        (G.tracialWordRepeatedOperator A D M S hsize U Y n a)
        (endpointWord d (fun _ : Fin n => r))) :=
  embedded_actions_repeated_word (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize U
    (G.tracialMatrixLeftRepresentation D M)
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext)
    (G.tracialMatrixLeftRepresentation_inclusion A D M S hsize U hword hτ)
    (G.tracialMatrixUnitaryRepresentation_inclusion A D M hgen hfaithful hext U hword hτ)
    Y hYL hYU n a d r

include hword hτ hYL hYU in
/-- The adjoint transforms by the adjoint of the same canonical coefficient. -/
theorem tracial_adjoint_repeated_word (n : ℕ) (a : WordMultiplicity (G.baseVector A 1) n)
    (d : G.baseSpace D) (r : centeredSubspace (G.baseVector D 1)) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        ((G.tracialWordRepeatedOperator A D M S hsize U Y n).adjoint a)
        (endpointWord d (fun _ : Fin n => r))) :=
  embedded_actions_adjoint_repeated_word (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize U
    (G.tracialMatrixLeftRepresentation D M)
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext)
    (G.tracialMatrixLeftRepresentation_inclusion A D M S hsize U hword hτ)
    (G.tracialMatrixUnitaryRepresentation_inclusion A D M hgen hfaithful hext U hword hτ)
    Y hYL hYU n a d r

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
