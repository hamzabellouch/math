import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryRayMatching
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryLeaf

namespace OAI

/-! # The template label supplies every generator action needed for the leaf bound -/

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

/-- Equal-set volume traces for the constructed ray actions imply the
whole nilpotent-leaf bound; the exceptional-ray choices are derived from
preservation of the actual support templates. -/
theorem nilpotent_leaf_bound_of_template_boundary_traces
    {P : Type*} [SimplyConnectedSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (R : ∀ i, M.RayBoundaryModel F (((α i).comp A.val.toLinearMap).comp θ))
    (U : ∀ i, Set (R i).cone.Q.carrier) (η : P → G → W)
    (rate B : Fin M.letterCount → ℝ) (hrate : ∀ i, 0 < rate i) (hB : ∀ i, 0 ≤ B i)
    (htrace : ∀ i p x y, (R i).action x '' U i = (R i).action y '' U i →
      |rate i * α i (η p x - η p y)| ≤ B i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p x (n : F.N.carrier),
      ‖η p (x * F.inclusionN n) - η p x‖ ≤ C := by
  obtain ⟨missing, hmissing⟩ := M.exists_template_missing_generators T F hunimod eW A R
  exact M.nilpotent_leaf_bound_from_boundary_traces T F hunimod eW hExpG realize haarN dynkinN
    b₀ γ₀ (fun i => rate i • α i) rate hrate (fun _ => rfl)
    (fun i => (R i).cone.Q.carrier) (fun i => (R i).action) U η missing B hB
    (fun i p x y he => by
      simpa only [LinearMap.smul_apply, smul_eq_mul] using htrace i p x y he)
    hmissing

end PolycyclicRecognition.CartanWordModel

end

end OAI
