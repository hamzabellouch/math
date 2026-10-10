import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryFamilyShadow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryMapFamily

namespace OAI

/-! # Continuous boundary families on the concrete ray quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
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

include hunimod hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- For concrete source and target ray quotients, the uniform sublinear
estimate constructs continuous boundary maps with a common compact shadow. -/
theorem exists_continuous_ray_boundary_family
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αS αT : W →L[ℝ] ℝ) (A : W →L[ℝ] W) (hα : αS = αT.comp A)
    (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (dynkinT : NilpotentDynkinExpansionInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (f : P → G → G) (hcont : ∀ p, Continuous (f p))
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
      ‖(height ((f p x)⁻¹ * f p (x * g))).toAdd - A ((height g).toAdd)‖ ≤
        ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αT (A v₀) < 0) :
    Nonempty (BoundaryMapFamily RS.action RT.action f) := by
  subst αS
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have hφ := fun d => cartan_action_eq_adjoint_of_published_realization
    T M F hExpG realize hbijN hbijD dynkinN d
  obtain ⟨B, K, hK, hB⟩ := M.exists_boundary_family_with_compact_shadow
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hφ hpath hKheight hLip
    αT RT.cone.Q RT.cone.maps.expQ RT.cone.maps.isExpQ
    RT.cone.maps.chartQ RT.cone.maps.chartQ_eq dynkinT
    RT.cone.maps.quotient RT.cone.maps.quotient_continuous RT.cone.maps.quotient_exp
    RT.factorAction RT.action RT.equivariant RT.action_eq
    A f hL hf hsub v₀ hv₀ RS.cone.maps.quotient RS.action
    RS.cone.maps.kernel_eq RS.stabilizer RS.orbit_surjective
  refine ⟨⟨B, K, hK, ?_, fun p x => (hB p x).2⟩⟩
  intro p
  apply M.continuous_boundary_map_of_ray_limits
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG b₀ γ₀ hφ hpath hKheight hLip
    αT RT.cone.Q RT.cone.maps.expQ RT.cone.maps.isExpQ
    RT.cone.maps.chartQ RT.cone.maps.chartQ_eq dynkinT
    RT.cone.maps.quotient RT.cone.maps.quotient_continuous RT.cone.maps.quotient_exp
    RT.factorAction RT.action RT.equivariant RT.action_eq A (f p) (hcont p) hL (hf p)
    (fun ε hε => by
      obtain ⟨D, hD, hb⟩ := hsub ε hε
      exact ⟨D, hD, hb p⟩) v₀ hv₀
    RT.cone.maps.sectionMap RT.cone.maps.sectionMap.continuous RT.cone.maps.section_rightInverse
    RS.cone.maps.quotient RS.cone.maps.quotient_continuous
    RS.cone.maps.sectionMap RS.cone.maps.sectionMap.continuous RS.cone.maps.section_rightInverse
    RS.factorAction RS.action RS.action_eq (B p)
  exact fun x => (hB p x).1

end PolycyclicRecognition.CartanWordModel

end

end OAI
