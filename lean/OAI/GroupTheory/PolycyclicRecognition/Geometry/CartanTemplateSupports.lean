import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportDirections

namespace OAI

/-! # Actual supporting Cartan directions for compact height templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Set

/-- All the independently supported generator exponents are realized by
actual Cartan vectors whose heights stay in the given compact template. -/
theorem exists_cartan_template_supports
    {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
    (M : CartanWordModel H) {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) :
    ∃ v : Fin M.letterCount → H,
      (∀ i, eW (heightProjection T.character (v i : L)) ∈ E) ∧
      M.templateSupportExponent v = (M.supportIn T hunimod eW).weightSupport E := by
  classical
  choose w hw hs using fun i => (M.supportIn T hunimod eW).exists_weightSupport_point hE hne i
  let v : Fin M.letterCount → H := fun i => cartanHeightSection T H (eW.symm (w i))
  have hv i : eW (heightProjection T.character (v i : L)) = w i := by simp [v]
  refine ⟨v, fun i => hv i ▸ hw i, ?_⟩
  funext i
  rw [hs i]
  change M.weight i (v i) = cartanHeightWeight T H (M.weight i) (eW.symm (w i))
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
