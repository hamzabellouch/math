import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSublinearRayComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryBoundedHeight

namespace OAI

/-! # Bounded height for a fixed template from published Lie inputs -/

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


variable (A : templateSymmetryGroup (M.supportIn T hunimod eW))

local notation "αT" => fun i => LinearMap.toContinuousLinearMap (SupportDatum.weight (supportIn M T hunimod eW) i)
local notation "A₀" => LinearEquiv.toContinuousLinearEquiv (Subtype.val A)
local notation "αS" => fun i => ContinuousLinearMap.comp (αT i) (ContinuousLinearEquiv.toContinuousLinearMap A₀)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))
local notation "χS" => fun i => LinearMap.comp (ContinuousLinearMap.toLinearMap (αS i)) θ
local notation "χT" => fun i => LinearMap.comp (ContinuousLinearMap.toLinearMap (αT i)) θ

include hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- Boundary comparisons are constructed from the published inputs, so the
fixed-label bounded estimate no longer assumes any boundary data. -/
theorem uniform_affine_bound_of_published_inputs_and_sublinear
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (metricInput : GeodesicMetricExistenceInput)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (sourceInputs : ∀ i, M.PolarConeModelInputs F (positiveWeightRay (χS i)))
    (targetInputs : ∀ i, M.PolarConeModelInputs F (positiveWeightRay (χT i)))
    (sourceDynkin : ∀ i (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay (χS i)))), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (targetDynkin : ∀ i (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay (χT i)))), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
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
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
      ‖(height (f p x)).toAdd - ((height (f p 1)).toAdd + A.val (height x).toAdd)‖ ≤ K := by
  classical
  have hex (i : Fin M.letterCount) := M.exists_published_boundary_comparison_of_sublinear
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD A i
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip
    (sourceInputs i) (targetInputs i) (sourceDynkin i) (targetDynkin i)
    f g hfcont hgcont hLf hLg hf hg hgf hfg hsubf hsubg
  choose RS RT hC using hex
  let C := fun i => Classical.choice (hC i)
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  apply M.uniform_affine_bound_of_boundary_comparisons T F hunimod eW height f A
    RS RT C hExpG realize hbijN chartD hchartD dynkinN metricInput
    (fun i => sourceDynkin i (RS i).cone.Q)
    (fun i => (sourceInputs i).haarQ (RS i).cone.Q) hheight haarN b₀ γ₀
  intro p ε hε
  obtain ⟨B, _, hb⟩ := hsubf ε hε
  refine ⟨B, fun x => ?_⟩
  have h := hb p 1 x
  simpa only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv, neg_add_eq_sub] using h

end PolycyclicRecognition.CartanWordModel

end

end OAI
