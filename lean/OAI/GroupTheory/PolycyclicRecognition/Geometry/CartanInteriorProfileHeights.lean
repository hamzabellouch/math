import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCompactSupportSlack

namespace OAI

/-! # Interior switch heights in the actual Cartan profile coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module Set

/-- A compact height template strictly inside the open profile domain
provides the interior-switch condition in every Cartan coordinate basis. -/
theorem exists_profile_coordinate_above_template
    {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
    (M : CartanWordModel H) {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (b : Basis (Fin (finrank ℝ H)) ℝ H)
    (E V : Set W) (hE : IsCompact E) (hne : E.Nonempty)
    (hV : IsOpen V) (hEV : E ⊆ V) (i : Fin M.letterCount) :
    ∃ z : Fin (finrank ℝ H) → ℝ,
      eW (heightProjection T.character (b.equivFun.symm z : L)) ∈ V ∧
      (M.supportIn T hunimod eW).weightSupport E i < M.weight i (b.equivFun.symm z) := by
  obtain ⟨h, hh, hweight⟩ := M.exists_cartan_height_above_compact_support
    T hunimod eW E V hE hne hV hEV i
  exact ⟨b.equivFun h, by simpa only [LinearEquiv.symm_apply_apply] using hh,
    by simpa only [LinearEquiv.symm_apply_apply] using hweight⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
