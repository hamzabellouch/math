import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFactorContraction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseNegativeQuotient

namespace OAI

/-! # Negative source chains give equality in the actual ray quotient

This combines the actual metric factorization, the compact-lift property,
and the proved ray contraction. Only the sublinear height comparison of
the coarse map remains a geometric premise.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W S : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [MetricSpace S] [One S]
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
/-- Polynomially many unit steps in a negative halfspace have asymptotic
images in the actual ray quotient under a coarse map with sublinear
height error. No contraction or metric-factor estimate is assumed here. -/
theorem negative_chain_quotient_difference_tendsto_one
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
    (sourceHeight : S → ℝ) (f : S → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |αW ((height (f x)).toAdd) - sourceHeight x| ≤ ε * dist 1 x + B)
    (m : ℕ → ℕ) (z : ℕ → ℕ → S)
    {R gap count : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap) (countDegree : ℕ)
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ count * (1 + (n : ℝ)) ^ countDegree)
    (hball : ∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hnegative : ∀ᶠ n in atTop, ∀ i ≤ m n, sourceHeight (z n i) ≤ -gap * n)
    (hstep : ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1) :
    Tendsto (fun n => (act (f (z n 0)) 1)⁻¹ * act (f (z n (m n))) 1)
      atTop (𝓝 (1 : Q.carrier)) := by
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
  let logD := cartanLog H F.D.equiv F.ExpD hbijD
  obtain ⟨B, degree, hB, hfactor⟩ := M.exists_metric_cartan_factor_bound
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip
  obtain ⟨K, hK, hKcover⟩ := exists_compact_factor_quotient_orbit F π hπcont α act hact
    (isCompact_closedBall (1 : G) (L + error))
  have hcontract := M.exists_ray_factor_compact_contraction
    T F αH Q ExpQ hbijQ chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ
  have hnil := Q.tangent_nilpotent (M.coneQuotient_nilpotent (positiveWeightRay αH))
  apply coarse_negative_chain_quotient_difference_of_compact_contraction
    F.inclusionN F.inclusionD π α act hact dynkinQ ExpQ hExpQ chartQ hchartQ hnil
    (fun d => ‖(finBasis ℝ H).equivFun (logD d)‖) (fun d => αH (logD d))
    sourceHeight (fun g => αW ((height g).toAdd)) f hL hf hsub hB degree
    ?_ K ?_ hK hcontract m z hR hgap countDegree hcount hball hnegative hstep
  · intro g
    obtain ⟨u, d, he, hh, hb⟩ := hfactor g
    refine ⟨u, d, he, norm_nonneg _, hb, ?_⟩
    change αW (eW (heightProjection T.character (logD d))) = _
    rw [← F.inclusionD_height T eW height hheight hbijD d, hh]
  · intro g hg
    apply hKcover g
    simpa only [Metric.mem_closedBall, dist_comm] using hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
