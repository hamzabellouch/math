import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSupportSlack
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents

namespace OAI

/-! # Interior switch heights for actual Cartan generator weights -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Set

/-- A compact template inside the open profile domain supplies the strict
height slack needed by `cartan_interior_neighbor_profiles_eq`, for every
actual generator weight. The Cartan representative is constructed. -/
theorem exists_cartan_height_above_compact_support
    {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
    (M : CartanWordModel H) {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (E U : Set W) (hE : IsCompact E) (hEne : E.Nonempty)
    (hU : IsOpen U) (hEU : E ⊆ U) (i : Fin M.letterCount) :
    ∃ h : H, eW (heightProjection T.character (h : L)) ∈ U ∧
      (M.supportIn T hunimod eW).weightSupport E i < M.weight i h := by
  let β : W →L[ℝ] ℝ :=
    ((cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap).toContinuousLinearMap
  have hβ : β ≠ 0 := by
    intro hz
    apply M.weight_nonzero i
    funext h
    have he := congrArg (fun f : W →L[ℝ] ℝ => f (eW (heightProjection T.character (h : L)))) hz
    simpa [β, cartanHeightWeight_projection] using he
  obtain ⟨y, hy, hys⟩ := exists_above_compact_support β hβ E U hE hEne hU hEU
  let h := cartanHeightSection T H (eW.symm y)
  have hh : eW (heightProjection T.character (h : L)) = y := by
    simp [h]
  refine ⟨h, hh.symm ▸ hy, ?_⟩
  have hval : β y = M.weight i h := rfl
  rw [hval] at hys
  exact hys

end PolycyclicRecognition.CartanWordModel

end

end OAI
