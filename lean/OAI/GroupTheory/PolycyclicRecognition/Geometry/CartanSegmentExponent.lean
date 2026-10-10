import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentVisits

namespace OAI

/-! # The exact source exponent of Cartan segment boxes -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (e : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The exponents of the actual segment construction equal the canonical
height-segment support exponents. -/
theorem boxCost_segment (v : H) :
    M.boxCost T hunimod e (segment ℝ 0 (e (heightProjection T.character v))) =
      fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w := by
  funext w
  unfold boxCost
  congr 1
  funext i
  rw [SupportDatum.weightSupport_segment]
  simp only [supportIn, SupportDatum.transport_weight_apply, supportDatum_weight,
    LinearEquiv.symm_apply_apply, cartanHeightWeight_projection, segmentSupportExponent]

/-- A maximizing segment box has precisely the support-profile exponent. -/
theorem maximizing_segment_exponent
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : H) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val) :
    columnBasisWeight
      (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val =
      (M.supportIn T hunimod e).segmentSupport (e (heightProjection T.character v)) := by
  rw [← M.boxCost_segment T hunimod e v] at hβ ⊢
  rw [M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod e b₀ _ β hβ,
    SupportDatum.templateSupport_segment]

end PolycyclicRecognition.CartanWordModel

end

end OAI
