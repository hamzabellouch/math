import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryGeneratorAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateInverseRays
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveRayPullback

namespace OAI

/-! # The missing generator ray for each template symmetry -/

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

omit [FiniteDimensional ℝ W] in
/-- The original Cartan generator characters are exactly the pullbacks of
the chosen Euclidean height coordinates. -/
theorem support_weight_comp_height (j : Fin M.letterCount) :
    (α j).comp θ = (M.weight j : H →ₗ[ℝ] ℝ) := by
  ext h
  change cartanHeightWeight T H (M.weight j)
    (eW.symm (eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) = _
  rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  rfl

/-- The template symmetry decides which one target ray can see a given
generator; every other boundary action kills that entire generator flow. -/
theorem exists_template_missing_generators
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (R : ∀ i, M.RayBoundaryModel F (((α i).comp A.val.toLinearMap).comp θ)) :
    ∃ missing : Fin M.letterCount → Fin M.letterCount,
      ∀ j i, α i ∉ positiveWeightRay (α (missing j)) →
        ∀ t : ℝ, (R i).action
          (ExpG (t • (M.letter j : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 := by
  classical
  have hn (j : Fin M.letterCount) : α j ≠ 0 := by
    intro hz
    exact M.sampling_weight_ne_zero T hunimod eW j
      (congrArg LinearMap.toContinuousLinearMap hz)
  choose missing c hc hmatch using fun j => templateSymmetry_inverse_weight_ray (M.supportIn T hunimod eW) A j (hn j)
  have hθ : Function.Surjective θ := by
    intro w
    refine ⟨cartanHeightSection T H (eW.symm w), ?_⟩
    change eW (heightProjection T.character
      ((cartanHeightSection T H (eW.symm w) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
    rw [cartanHeightSection_height, eW.apply_symm_apply]
  let θA := A.val.toLinearMap.comp θ
  have hθA : Function.Surjective θA := A.val.surjective.comp hθ
  refine ⟨missing, ?_⟩
  intro j i hi t
  have hm : (α (missing j)).comp θA = c j • (M.weight j : H →ₗ[ℝ] ℝ) := by
    change ((α (missing j)).comp A.val.toLinearMap).comp θ = _
    rw [hmatch j, LinearMap.smul_comp, M.support_weight_comp_height T hunimod eW j]
  have hout := outside_ray_of_surjective_pullback θA hθA
    (α (missing j)) (α i) (M.weight j : H →ₗ[ℝ] ℝ) (hc j) hm hi
  exact M.outside_generator_boundary_action_eq_one F
    (((α i).comp A.val.toLinearMap).comp θ) (R i).cone.Q (R i).cone.maps.expQ
    (R i).cone.maps.isExpQ (R i).cone.maps.quotient (R i).cone.maps.quotient_exp
    (R i).factorAction (R i).action (R i).action_eq j hout t

end PolycyclicRecognition.CartanWordModel

end

end OAI
