import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDirectionalVisits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SegmentSupportTimes

namespace OAI

/-! # The prescribed segment endpoints are actual root support positions -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The support time is chosen on the original horizontal line. Its scaled
Cartan direction has the exact root height required by the switch estimate. -/
theorem segment_visit_direction_support
    (v : H) (w₀ : W) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) (i : Fin M.letterCount) :
    let u := eW (heightProjection T.character (v : L))
    let θ := (M.supportIn T hunimod eW).segmentSupportTime u T₀ i
    cartanHeightWeight T H (M.weight i)
      (eW.symm (w₀ + eW (heightProjection T.character ((θ • v : H) : L)))) =
      (M.supportIn T hunimod eW).weightSupport (segment ℝ w₀ (w₀ + T₀ • u)) i := by
  dsimp only
  have hh := (M.supportIn T hunimod eW).weight_at_segmentSupportTime w₀
    (eW (heightProjection T.character (v : L))) hT₀ i
  simpa only [map_smul, SetLike.val_smul, supportIn,
    SupportDatum.transport_weight_apply, supportDatum_weight] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
