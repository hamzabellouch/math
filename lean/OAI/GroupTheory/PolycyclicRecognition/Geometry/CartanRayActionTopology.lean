import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFactorContraction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialAutomorphismTopology

namespace OAI

/-! # Continuity of the actual ray quotient action -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable (α₀ : H →ₗ[ℝ] ℝ)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
  (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
  (hbijQ : Function.Bijective ExpQ)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (hchartQ : ∀ v, chartQ v = ExpQ v)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (π : F.N.carrier →* Q.carrier)
  (hπ : ∀ x : cartanRootIdeal H,
    π (F.ExpN (F.N.equiv x)) = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
  (α : F.D.carrier →* MulAut Q.carrier)
  (hα : ∀ d n, α d (π n) = π (F.action d n))
  (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))

include hbijQ hchartQ hπ hα hφ in
/-- Each actual Cartan factor acts continuously on the ray quotient.
This follows from its previously identified exponential conjugation. -/
theorem continuous_ray_factor_action (d : F.D.carrier) : Continuous (α d) := by
  have heq : (α d : Q.carrier → Q.carrier) = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) := by
    funext q
    exact M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ d q
  rw [heq]
  exact continuous_exponentialConjugate Q.equiv ExpQ hbijQ chartQ hchartQ _

include hbijQ hchartQ hπ hα hφ in
/-- Every fixed ambient group element acts continuously; no continuity
assumption on a chosen factorization is needed. -/
theorem continuous_ambient_ray_action
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (g : G) : Continuous (act g) := by
  let _ : IsTopologicalGroup Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Q.modelSpace)) ⊤
  obtain ⟨⟨u, d⟩, he⟩ := F.surjective g
  have heq : (act g : Q.carrier → Q.carrier) = fun q => π u * α d q := by
    funext q
    rw [← he]
    exact hact u d q
  rw [heq]
  exact continuous_const.mul (M.continuous_ray_factor_action T F α₀ Q ExpQ hbijQ
    chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ d)

end PolycyclicRecognition.CartanWordModel

end

end OAI
