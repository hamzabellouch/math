import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryLeafTemplate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryComparison

namespace OAI

/-! # The leaf bound from the constructed boundary volume comparisons -/

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

/-- The compact-shadow volume data provide all equal-set traces; there
is no independent generator-action or leaf-bound premise. -/
theorem nilpotent_leaf_bound_of_boundary_comparisons
    {P : Type*} [SimplyConnectedSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (height : G →* Multiplicative W) (f : P → G → G)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (RS : ∀ i, M.RayBoundaryModel F (((α i).comp A.val.toLinearMap).comp θ))
    (RT : ∀ i, M.RayBoundaryModel F ((α i).comp θ))
    (C : ∀ i, BoundaryVolumeComparison (RS i).action (RT i).action
      (((α i).toContinuousLinearMap).comp A.val.toContinuousLinearEquiv.toContinuousLinearMap)
      (α i).toContinuousLinearMap height f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ p x (n : F.N.carrier),
      ‖(height (f p (x * F.inclusionN n))).toAdd - (height (f p x)).toAdd‖ ≤ L := by
  apply M.nilpotent_leaf_bound_of_template_boundary_traces T F hunimod eW
    hExpG realize haarN dynkinN b₀ γ₀ A RS
    (fun i => ((C i).window : Set (RS i).cone.Q.carrier))
    (fun p x => (height (f p x)).toAdd)
    (fun i => (C i).targetRate) (fun i => (C i).traceBound)
    (fun i => (C i).targetRate_pos) (fun i => (C i).traceBound_nonneg)
  intro i p x y he
  have h := (C i).equal_set_trace p x y he
  simpa only [LinearMap.coe_toContinuousLinearMap', map_sub, mul_sub] using h

end PolycyclicRecognition.CartanWordModel

end

end OAI
