import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFactorContraction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseRayQuotientLimits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NegativePathWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeights

namespace OAI

/-! # Common compact shadows of actual centered Cartan rays -/

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
/-- Uniform sublinear height control on a centered family gives a common
compact limit set for its actual projected canonical rays. All polynomial
factor bounds and quotient contraction estimates are derived here. -/
theorem centered_ray_quotient_compact_limits
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
    (hExpG : IsGroupExponential ExpG)
    (A : W →L[ℝ] W) (f : P → G → G) (hcenter : ∀ x, f x 1 = 1)
    {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p g,
      ‖(height (f p g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0) :
    let ray := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (g : P → Q.carrier) (K : Set Q.carrier), IsCompact K ∧ (∀ p, g p ∈ K) ∧
      ∀ p, Tendsto (fun n => act (f p (ray n)) 1) atTop (𝓝 (g p)) := by
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
  let h₀ := (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  let ray := fun n : ℕ => ExpG ((n : ℝ) • h₀)
  let R := dist (1 : G) (ExpG h₀)
  let β := αW.comp A
  have hray (n : ℕ) : dist 1 (ray n) ≤ R * n := by
    have hh := one_parameter_nat_dist_le (fun t => ExpG (t • h₀))
      (by simpa only [zero_smul] using hExpG.map_zero) (hExpG.map_add_smul h₀) n
    simpa only [one_smul, mul_comm] using hh
  have hnegative (n : ℕ) : β ((height (ray n)).toAdd) ≤ -(-β v₀) * n := by
    have hh : (height (ray n)).toAdd = (n : ℝ) • v₀ := by
      change (height (ExpG ((n : ℝ) • h₀))).toAdd = _
      rw [hheight]
      simp [h₀]
    rw [hh, map_smul, smul_eq_mul]
    nlinarith
  have hsteps (n : ℕ) : dist (ray n) (ray (n + 1)) ≤ R := by
    have he : ray (n + 1) = ray n * ExpG h₀ := by
      dsimp only [ray]
      rw [Nat.cast_add, Nat.cast_one, hExpG.map_add_smul, one_smul]
    rw [he]
    have hd : dist (ray n) (ray n * ExpG h₀) = R := by
      simpa only [mul_one] using dist_mul_left (ray n) (1 : G) (ExpG h₀)
    exact hd.le
  have hscalar := scalar_sublinear_error (fun x : P × G => dist 1 x.2)
    (fun _ => dist_nonneg) (fun x => (height (f x.1 x.2)).toAdd)
    (fun x => A ((height x.2).toAdd)) αW (by
      intro ε hε
      obtain ⟨B, hB, hb⟩ := hsub ε hε
      exact ⟨B, hB, fun x => hb x.1 x.2⟩)
  obtain ⟨B, degree, hB, hfactor⟩ := M.exists_metric_cartan_factor_bound
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ hφ hpath hKheight hLip
  obtain ⟨b, p, rate, hrate, hcontract⟩ := M.exists_ray_factor_compact_contraction
    T F αH Q ExpQ hbijQ chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ
  have hnil := Q.tangent_nilpotent (M.coneQuotient_nilpotent (positiveWeightRay αH))
  apply centered_coarse_ray_quotient_limits F.inclusionN F.inclusionD π α act hact
    dynkinQ ExpQ hExpQ chartQ hchartQ hnil b
    (fun d => ‖(finBasis ℝ H).equivFun (logD d)‖) (fun d => αH (logD d))
    (fun x => β ((height x).toAdd)) (fun x => αW ((height x).toAdd))
    f hcenter hL (show 0 ≤ R from dist_nonneg) (neg_pos.mpr hv₀) hB hrate hf
    ?_ ray hray hnegative hsteps degree p ?_ ?_ hcontract
  · intro ε hε
    obtain ⟨B, hB, hb⟩ := hscalar ε hε
    exact ⟨B, hB, fun x y => hb (x, y)⟩
  · intro g
    obtain ⟨u, d, he, hh, hb⟩ := hfactor g
    refine ⟨u, d, he, norm_nonneg _, hb, ?_⟩
    change αW (eW (heightProjection T.character (logD d))) = _
    rw [← F.inclusionD_height T eW height hheight hbijD d, hh]
  · intro r
    obtain ⟨K, hK, hKcover⟩ := exists_compact_factor_quotient_orbit F π hπcont α act hact
      (isCompact_closedBall (1 : G) r)
    exact ⟨K, hK, fun g hg => hKcover g (by simpa only [Metric.mem_closedBall, dist_comm] using hg)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
