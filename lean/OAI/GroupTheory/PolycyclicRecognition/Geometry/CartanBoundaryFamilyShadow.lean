import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundaryShadow

namespace OAI

/-! # A common compact shadow for a family with fixed linear height label -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
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

include hunimod hheight dynkinD in
/-- The common centered sublinear estimate supplies one compact boundary
shadow for the entire fixed-label family, uniformly over its basepoints. -/
theorem exists_boundary_family_with_compact_shadow
    [SimplyConnectedSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (A : W →L[ℝ] W) (f : P → G → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
      ‖(height ((f p x)⁻¹ * f p (x * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    {S : Type*} [Group S] (πS : F.N.carrier →* S) (actS : G →* Equiv.Perm S)
    (hkerS : (πS.ker : Set F.N.carrier) = F.ExpN '' (F.N.equiv ''
      (M.coneWordIdeal (positiveWeightRay ((αW.comp A).toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
        Set (cartanRootIdeal H))))
    (hstab : ∀ g, actS g 1 = 1 ↔ ∃ n d,
      n ∈ πS.ker ∧ F.inclusionN n * F.inclusionD d = g)
    (hcover : Function.Surjective (fun g => actS g 1)) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (B : P → S → Q.carrier) (K : Set Q.carrier), IsCompact K ∧ ∀ p x,
      Tendsto (fun n => act (f p (x * ray n)) 1) atTop (𝓝 (B p (actS x 1))) ∧
      ∃ z ∈ K, B p (actS x 1) = act (f p x) z := by
  classical
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  let centered := fun (p : P × G) g => (f p.1 p.2)⁻¹ * f p.1 (p.2 * g)
  have hcenter (p : P × G) : centered p 1 = 1 := by simp [centered]
  have hcoarse (p : P × G) x y :
      dist (centered p x) (centered p y) ≤ L * dist x y + error :=
    centered_coarse_lipschitz (f p.1) (hf p.1) p.2 x y
  have hsub' : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height (centered p g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B := by
    intro ε hε
    obtain ⟨B, hB, hb⟩ := hsub ε hε
    exact ⟨B, hB, fun p g => hb p.1 p.2 g⟩
  obtain ⟨k, K, hK, hkK, hk⟩ := M.centered_ray_quotient_compact_limits
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip αW Q ExpQ hExpQ chartQ hchartQ dynkinQ
    π hπcont hπ α act hα hact hExpG A centered hcenter hL hcoarse hsub' v₀ hv₀
  have habsolute p := absolute_height_sublinear_of_centered_uniform height A (f p)
    (by
      intro ε hε
      obtain ⟨B, hB, hb⟩ := hsub ε hε
      exact ⟨B, hB, fun x g => hb p x g⟩)
  let αH := αW.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  have hbijQ : Function.Bijective ExpQ := by
    rw [← show chartQ = ExpQ from funext hchartQ]
    exact chartQ.bijective
  have hcontinuous := M.continuous_ambient_ray_action T F αH Q ExpQ hbijQ chartQ hchartQ
    hbijN hbijD dynkinN π hπ α hα hφ act hact
  have hex p := boundary_shadow_of_centered_limits act hcontinuous
    (fun g => actS g 1) hcover (f p)
    (fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    K (fun x => k (p, x)) (fun x => hkK (p, x)) (fun x => hk (p, x))
    (fun x y he => M.orbit_fiber_quotient_difference_tendsto_one
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
      hExpG realize haarN haarD b₀ γ₀ hφ hpath hKheight hLip
      αW Q ExpQ hExpQ chartQ hchartQ dynkinQ π hπcont hπ α act hα hact
      A (f p) hL (hf p) (habsolute p) v₀ hv₀ πS actS hkerS hstab x y he)
  choose B hB using hex
  exact ⟨B, K, hK, hB⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
