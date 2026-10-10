import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanContinuousRayLimits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundedCenteredHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactLiftQuotient

namespace OAI

/-! # Continuity of the constructed Cartan ray limits -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
/-- Uniform summable logarithmic increments on compact parameter sets make
an already constructed boundary ray limit continuous. -/
theorem continuous_boundary_ray_limit
    (hExpG : IsGroupExponential ExpG)
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
    (A : W →L[ℝ] W) (f : G → G) (hfcont : Continuous f)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height ((f p)⁻¹ * f (p * g))).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    (s : Q.carrier → F.N.carrier) (hs : Continuous s)
    (hsection : Function.RightInverse s π)
    (b : G → Q.carrier)
    (hlimit : ∀ x, Tendsto (fun n : ℕ => act (f (x *
      ExpG ((n : ℝ) • (cartanHeightSection T H (eW.symm v₀) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))) 1) atTop (𝓝 (b x))) :
    Continuous b := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have horbit := (F.orbitMap_isQuotientMap π hπcont s hs hsection α act hact).continuous
  apply continuous_from_compactlyGeneratedSpace b
  intro P _ _ _ center hcenter
  have hc : IsCompact (Set.range (f ∘ center)) := isCompact_range (hfcont.comp hcenter)
  obtain ⟨start, hstart⟩ := (Metric.isBounded_iff_subset_closedBall (1 : G)).mp hc.isBounded
  have hbound (p : P) : dist 1 (f (center p)) ≤ start := by
    have hh := hstart (Set.mem_range_self p)
    simpa only [Function.comp_apply, Metric.mem_closedBall, dist_comm] using hh
  have hfamily := bounded_family_height_of_centered_uniform height A f hKheight hLip hsub center hbound
  have hcoarse (p : P) (x y : G) :
      dist (f (center p * x)) (f (center p * y)) ≤ L * dist x y + error := by
    simpa only [dist_mul_left] using hf (center p * x) (center p * y)
  have hinitial (p : P) : dist 1 (f (center p * 1)) ≤ start := by
    simpa only [mul_one] using hbound p
  have hcontinuous (n : ℕ) : Continuous (fun p => act (f (center p *
      ExpG ((n : ℝ) • (cartanHeightSection T H (eW.symm v₀) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)))) 1) :=
    horbit.comp (hfcont.comp (hcenter.mul continuous_const))
  obtain ⟨g, K, hK, hg, hgK, hglimit⟩ := M.continuous_bounded_ray_quotient_limits
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip αW Q ExpQ hExpQ chartQ hchartQ dynkinQ
    π hπcont hπ α act hα hact hExpG A (fun p x => f (center p * x))
    hinitial hL hcoarse hfamily v₀ hv₀ hcontinuous
  have he (p : P) : g p = b (center p) := tendsto_nhds_unique (hglimit p) (hlimit (center p))
  have hfunctions : g = b ∘ center := funext he
  rwa [hfunctions] at hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
