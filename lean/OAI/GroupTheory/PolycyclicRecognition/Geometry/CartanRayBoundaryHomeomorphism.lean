import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryFamily
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryInverse

namespace OAI

/-! # Actual boundary homeomorphisms for coarse inverse families -/

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
/-- Applying the ray construction in both directions gives homeomorphisms,
with common compact forward and inverse shadows. -/
theorem exists_ray_boundary_family_homeomorphisms
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
    (αS αT : W →L[ℝ] ℝ) (A : W ≃L[ℝ] W)
    (hα : αS = αT.comp A.toContinuousLinearMap)
    (RS : M.RayBoundaryModel F (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (RT : M.RayBoundaryModel F (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
    (dynkinS : NilpotentDynkinExpansionInput RS.cone.Q.modelSpace RS.cone.Q.carrier)
    (dynkinT : NilpotentDynkinExpansionInput RT.cone.Q.modelSpace RT.cone.Q.carrier)
    (f g : P → G → G) (hfcont : ∀ p, Continuous (f p)) (hgcont : ∀ p, Continuous (g p))
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (hsubf : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((f p x)⁻¹ * f p (x * y))).toAdd - A ((height y).toAdd)‖ ≤
        ε * dist 1 y + B)
    (hsubg : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((g p x)⁻¹ * g p (x * y))).toAdd - A.symm ((height y).toAdd)‖ ≤
        ε * dist 1 y + B)
    (v₀ : W) (hv₀ : αS v₀ < 0) :
    ∃ (B : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier)
      (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier),
      IsCompact KS ∧ IsCompact KT ∧
      (∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z) ∧
      (∀ p x, ∃ z ∈ KS, (B p).symm (RT.action x 1) = RS.action (g p x) z) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have htarget : αT (A v₀) < 0 := by
    simpa only [hα, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using hv₀
  have hαinv : αT = αS.comp A.symm.toContinuousLinearMap := by
    rw [hα]
    ext w
    simp
  have hinverse : αS (A.symm (A v₀)) < 0 := by simpa using hv₀
  let forward : BoundaryMapFamily RS.action RT.action f := Classical.choice <|
    M.exists_continuous_ray_boundary_family
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip αS αT
    A.toContinuousLinearMap hα RS RT dynkinT f hfcont hLf hf hsubf v₀ htarget
  let inverse : BoundaryMapFamily RT.action RS.action g := Classical.choice <|
    M.exists_continuous_ray_boundary_family
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip αT αS
    A.symm.toContinuousLinearMap hαinv RT RS dynkinS g hgcont hLg hg hsubg (A v₀) hinverse
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have hvS : (αS.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))
      (cartanHeightSection T H (eW.symm v₀)) < 0 := by
    change αS (eW (heightProjection T.character
      ((cartanHeightSection T H (eW.symm v₀) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) < 0
    simpa only [cartanHeightSection_height, LinearEquiv.apply_symm_apply] using hv₀
  have hvT : (αT.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))
      (cartanHeightSection T H (eW.symm (A v₀))) < 0 := by
    change αT (eW (heightProjection T.character
      ((cartanHeightSection T H (eW.symm (A v₀)) : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) < 0
    simpa only [cartanHeightSection_height, LinearEquiv.apply_symm_apply] using htarget
  obtain ⟨D, hD, hDinv⟩ := M.ray_boundary_homeomorphisms_of_compact_shadows
    T F hExpG realize hbijN hbijD dynkinN _ _ RS RT
    (cartanHeightSection T H (eW.symm v₀))
    (cartanHeightSection T H (eW.symm (A v₀))) hvS hvT
    forward.map inverse.map forward.continuous inverse.continuous f g hLf hLg hf hg hgf hfg
    inverse.compact forward.compact inverse.isCompact forward.isCompact forward.shadow inverse.shadow
  refine ⟨D, inverse.compact, forward.compact, inverse.isCompact, forward.isCompact, ?_, ?_⟩
  · intro p x
    simpa only [hD] using forward.shadow p x
  · intro p x
    simpa only [hDinv] using inverse.shadow p x

end PolycyclicRecognition.CartanWordModel

end

end OAI
