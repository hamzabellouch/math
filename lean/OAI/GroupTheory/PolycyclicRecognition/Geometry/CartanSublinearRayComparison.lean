import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryHomeomorphism
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryRetainedRay

namespace OAI

/-! # Constructing one boundary comparison from the published inputs and sublinear height -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

variable (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount)

local notation "αT" => LinearMap.toContinuousLinearMap (SupportDatum.weight (supportIn M T hunimod eW) i)
local notation "A₀" => LinearEquiv.toContinuousLinearEquiv (Subtype.val A)
local notation "αS" => ContinuousLinearMap.comp αT (ContinuousLinearEquiv.toContinuousLinearMap A₀)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))
local notation "χS" => LinearMap.comp (ContinuousLinearMap.toLinearMap αS) θ
local notation "χT" => LinearMap.comp (ContinuousLinearMap.toLinearMap αT) θ

include hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- All ray models, actions, boundary maps, and volume comparisons are
constructed here. Only the previously established sublinear estimates and
precisely stated published Lie inputs enter the construction. -/
theorem exists_published_boundary_comparison_of_sublinear
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (sourceInputs : M.PolarConeModelInputs F (positiveWeightRay χS))
    (targetInputs : M.PolarConeModelInputs F (positiveWeightRay χT))
    (sourceDynkin : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay χS)), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (targetDynkin : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay χT)), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (f g : P → G → G) (hfcont : ∀ p, Continuous (f p)) (hgcont : ∀ p, Continuous (g p))
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (hsubf : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((f p x)⁻¹ * f p (x * y))).toAdd - A.val ((height y).toAdd)‖ ≤ ε * dist 1 y + B)
    (hsubg : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((g p x)⁻¹ * g p (x * y))).toAdd - A.val.symm ((height y).toAdd)‖ ≤ ε * dist 1 y + B) :
    ∃ (RS : M.RayBoundaryModel F χS) (RT : M.RayBoundaryModel F χT),
      Nonempty (RayBoundaryComparison RS RT height f) := by
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  obtain ⟨hχS, jS, hjS⟩ := M.exists_retained_generator_for_template_ray T hunimod eW A i
  have hχT : χT = (M.weight i : H →ₗ[ℝ] ℝ) := M.support_weight_comp_height T hunimod eW i
  have hχTne : χT ≠ 0 := by
    rw [hχT]
    intro hz
    apply M.weight_nonzero i
    funext h
    exact LinearMap.congr_fun hz h
  let RS : M.RayBoundaryModel F χS := Classical.choice <|
    M.nonempty_rayBoundaryModel_of_published_inputs F χS T hExpG realize haarN
      hbijN hbijD dynkinN sourceInputs hχS
  let RT : M.RayBoundaryModel F χT := Classical.choice <|
    M.nonempty_rayBoundaryModel_of_published_inputs F χT T hExpG realize haarN
      hbijN hbijD dynkinN targetInputs hχTne
  obtain ⟨w, hw⟩ := M.exists_negative_sampling_weight T hunimod eW i
  have hv : αS ((A₀).symm w) < 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, LinearMap.coe_toContinuousLinearMap'] using hw
  obtain ⟨B, KS, KT, hKS, hKT, hB, hC⟩ := M.exists_ray_boundary_family_homeomorphisms
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip αS αT A₀ rfl RS RT
    (sourceDynkin RS.cone.Q) (targetDynkin RT.cone.Q)
    f g hfcont hgcont hLf hLg hf hg hgf hfg hsubf hsubg ((A₀).symm w) hv
  refine ⟨RS, RT, ?_⟩
  exact nonempty_rayBoundaryComparison_of_shadows RS RT height f hExpG realize hbijN hbijD
    dynkinN (sourceInputs.haarQ RS.cone.Q) (targetInputs.haarQ RT.cone.Q) hheight
    jS i hjS (by rw [hχT]; exact positiveWeightRay_self _)
    B g hLf hLg hf hg hgf KS KT hKS hKT hB hC

end PolycyclicRecognition.CartanWordModel

end

end OAI
