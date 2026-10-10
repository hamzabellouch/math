import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryRayMatching

namespace OAI

/-! # Retained generators and negative height directions for the actual rays -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

local notation "α" => SupportDatum.weight (supportIn M T hunimod eW)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))

/-- A pulled-back target weight retains a genuine source generator. This
supplies both the nonzero ray needed for the descended action and the strict
positivity of its Haar character. -/
theorem exists_retained_generator_for_template_ray
    (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount) :
    let χ := ((α i).comp A.val.toLinearMap).comp θ
    χ ≠ 0 ∧ ∃ j : Fin M.letterCount,
      (M.weight j : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay χ := by
  have hn : α i ≠ 0 := by
    intro hz
    exact M.sampling_weight_ne_zero T hunimod eW i
      (congrArg LinearMap.toContinuousLinearMap hz)
  obtain ⟨j, r, hr, he⟩ := templateSymmetry_weight_ray (M.supportIn T hunimod eW) A i hn
  have hsource : ((α i).comp A.val.toLinearMap).comp θ = r • (M.weight j : H →ₗ[ℝ] ℝ) := by
    rw [he, LinearMap.smul_comp, M.support_weight_comp_height T hunimod eW j]
  have hnj : (M.weight j : H →ₗ[ℝ] ℝ) ≠ 0 := by
    intro hj
    apply M.weight_nonzero j
    funext h
    exact LinearMap.congr_fun hj h
  refine ⟨?_, j, r⁻¹, inv_pos.mpr hr, ?_⟩
  · rw [hsource]
    exact smul_ne_zero hr.ne' hnj
  · rw [hsource, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The selected nonzero target weight has a contracting direction in
height space. -/
theorem exists_negative_sampling_weight (i : Fin M.letterCount) :
    ∃ w : W, α i w < 0 := by
  have hn : α i ≠ 0 := by
    intro hz
    exact M.sampling_weight_ne_zero T hunimod eW i
      (congrArg LinearMap.toContinuousLinearMap hz)
  have hex : ∃ w : W, α i w ≠ 0 := by
    by_contra h
    apply hn
    ext w
    exact not_ne_iff.mp (not_exists.mp h w)
  obtain ⟨w, hw⟩ := hex
  by_cases hneg : α i w < 0
  · exact ⟨w, hneg⟩
  · exact ⟨-w, by rw [map_neg]; exact neg_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hw))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
