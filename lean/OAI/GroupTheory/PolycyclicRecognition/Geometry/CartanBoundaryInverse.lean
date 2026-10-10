import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayCompactCollapse
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryInverseShadow

namespace OAI

/-! # The inverse identity for the constructed ray-boundary maps -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
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
/-- Coarse inverse maps and the actual compact shadows force the boundary
composition to be the identity. No inverse property of the boundary maps
is assumed. -/
theorem boundary_left_inverse_of_actual_compact_shadows
    (hExpQ : IsGroupExponential ExpQ) (hπcont : Continuous π)
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (v : H) (hv : α₀ v < 0)
    {R : Type*} [One R] [TopologicalSpace R] (actR : G →* Equiv.Perm R)
    (B : Q.carrier → R) (C : R → Q.carrier) (f g : G → G)
    {Lg error E : ℝ} (hLg : 0 ≤ Lg)
    (hg : ∀ x y, dist (g x) (g y) ≤ Lg * dist x y + error)
    (hinv : ∀ x, dist (g (f x)) x ≤ E)
    (σ : Q.carrier → G) (hσ : Continuous σ) (hsection : ∀ q, act (σ q) 1 = q)
    (σR : R → G) (hσR : Continuous σR) (hsectionR : ∀ q, actR (σR q) 1 = q)
    (KR : Set R) (hKR : IsCompact KR) (KQ : Set Q.carrier) (hKQ : IsCompact KQ)
    (hB : ∀ x, ∃ q ∈ KR, B (act x 1) = actR (f x) q)
    (hC : ∀ x, ∃ q ∈ KQ, C (actR x 1) = act (g x) q) :
    Function.LeftInverse C B := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨KT, hKT, hBT⟩ := compact_lift_boundary_shadow act actR B f σR hσR hsectionR KR hKR hB
  obtain ⟨KS, hKS, hCS⟩ := compact_lift_boundary_shadow actR act C g σ hσ hsection KQ hKQ hC
  have hshadow := inverse_boundary_compact_shadow act actR B C f g hLg hg hinv KT KS hKT hKS hBT hCS
  obtain ⟨hfix, hcontract⟩ := M.ambient_ray_fixes_one_and_contracts_compact_orbits
    T F α₀ Q ExpQ hbijQ chartQ hchartQ hbijN hbijD dynkinN π hπ α hα hφ
    hExpQ hπcont act hact v hv
  have hcontinuous := M.continuous_ambient_ray_action T F α₀ Q ExpQ hbijQ chartQ hchartQ
    hbijN hbijD dynkinN π hπ α hα hφ act hact
  have hid := boundary_left_inverse_of_compact_shadow act hcontinuous B C
    (fun n : ℕ => ExpG (((n : ℝ) • v : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    hfix hcontract hshadow
  intro q
  simpa only [hsection] using hid (σ q)

end PolycyclicRecognition.CartanWordModel

end

end OAI
