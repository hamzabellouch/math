import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialCellMass
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfiles

namespace OAI

/-! # Probability on the actual translated Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit [SimplyConnectedSpace G] in
/-- Every translated unit Cartan box is Borel and has positive finite
measure for the same canonical Haar normalization used by recurrence. -/
theorem translated_groupBox_cell_properties
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := (fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
    MeasurableSet Q ∧ μ Q ≠ 0 ∧ μ Q ≠ ∞ := by
  dsimp only
  let b := M.boxBasis T hunimod eW E β r
  let ψ := fun y => ((F.ExpN ∘ F.N.equiv) ∘ b.equivFun.symm) y * k
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  have heq : (fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 =
      ψ '' cube := by
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one, ← image_comp]
    rfl
  rw [heq]
  have hmeas := measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN
    chartN hchartN b k
  have hmass := translated_exponential_cell_mass haarN F.N.equiv (cartanRootIdeal_nilpotent H T)
    F.ExpN F.isExpN chartN hchartN M.letter M.wordList b₀ β
    (M.boxCost T hunimod eW E) r k cube
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
  refine ⟨hmeas.measurableSet_image.mpr measurableSet_Icc, ?_, hmass.2⟩
  exact (ENNReal.toReal_pos_iff.mp hmass.1).1.ne'

/-- The normalized restriction to the actual translated unit box. -/
def translatedGroupBoxProbability
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k : F.N.carrier) : ProbabilityMeasure F.N.carrier :=
  cellProbabilityMeasure
    (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
    ((fun y => y * k) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1)
    (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ E β r k).2.1
    (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀ E β r k).2.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
