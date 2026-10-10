import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIdealFiberAsymptotics
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OrbitFiberAsymptotics
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorAsymptotics
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNegativeChainAsymptotics
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFiberPaths

namespace OAI

/-! # Asymptotic equality on fibers of the actual boundary orbit -/

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
/-- The ideal and Cartan-factor path estimates imply asymptotic equality
for all representatives of the same source boundary point. The source
stabilizer and projection kernel are the actual algebraic constructions. -/
theorem orbit_fiber_quotient_difference_tendsto_one
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
    (A : W →L[ℝ] W) (f : G → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖(height (f g)).toAdd - A ((height g).toAdd)‖ ≤ ε * dist 1 g + B)
    (v₀ : W) (hv₀ : αW (A v₀) < 0)
    {S : Type*} [Group S] (πS : F.N.carrier →* S) (actS : G →* Equiv.Perm S)
    (hkerS : (πS.ker : Set F.N.carrier) = F.ExpN '' (F.N.equiv ''
      (M.coneWordIdeal (positiveWeightRay ((αW.comp A).toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) :
        Set (cartanRootIdeal H))))
    (hstab : ∀ g, actS g 1 = 1 ↔ ∃ n d,
      n ∈ πS.ker ∧ F.inclusionN n * F.inclusionD d = g)
    (g g' : G) (hg : actS g 1 = actS g' 1) :
    let d := fun n : ℕ => ExpG ((n : ℝ) •
      (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    Tendsto (fun n => (act (f (g * d n)) 1)⁻¹ * act (f (g' * d n)) 1)
      atTop (𝓝 (1 : Q.carrier)) := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  let β := αW.comp A
  let I := M.coneWordIdeal (positiveWeightRay (β.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))
  let ι : I → G := fun x => F.inclusionN (F.ExpN (F.N.equiv (x : cartanRootIdeal H)))
  have hstab' (k : G) : actS k 1 = 1 ↔ ∃ (x : I) (d : F.D.carrier), ι x * F.inclusionD d = k := by
    rw [hstab]
    constructor
    · rintro ⟨n, d, hn, he⟩
      have hn' : n ∈ F.ExpN '' (F.N.equiv '' (I : Set (cartanRootIdeal H))) := by
        rw [← hkerS]
        exact hn
      obtain ⟨v, ⟨x, hx, hv⟩, hn''⟩ := hn'
      subst v
      subst n
      exact ⟨⟨x, hx⟩, d, he⟩
    · rintro ⟨x, d, he⟩
      refine ⟨F.ExpN (F.N.equiv (x : cartanRootIdeal H)), d, ?_, he⟩
      change F.ExpN (F.N.equiv (x : cartanRootIdeal H)) ∈ (πS.ker : Set F.N.carrier)
      rw [hkerS]
      exact ⟨F.N.equiv (x : cartanRootIdeal H), ⟨x, x.property, rfl⟩, rfl⟩
  let ray := fun n : ℕ => ExpG ((n : ℝ) •
    (cartanHeightSection T H (eW.symm v₀) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  apply orbit_fiber_asymptotic_of_stabilizer actS ι F.inclusionD hstab'
    (fun k n => act (f (k * ray n)) 1) ?_ ?_ g g' hg
  · intro k x
    have hh := M.ideal_fiber_quotient_difference_tendsto_one
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
      hExpG realize haarN haarD b₀ γ₀ hφ hpath hKheight hLip
      αW Q ExpQ hExpQ chartQ hchartQ dynkinQ π hπcont hπ α act hα hact
      A f hL hf hsub v₀ hv₀ x k
    simpa only [ray, ι, mul_assoc] using hh
  · intro k d
    have hh := M.cartan_fiber_quotient_difference_tendsto_one
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
      b₀ γ₀ hφ hpath hKheight hLip
      αW Q ExpQ hExpQ chartQ hchartQ dynkinQ π hπcont hπ α act hα hact
      A f hL hf hsub v₀ hv₀ d k
    simpa only [ray, mul_assoc] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
