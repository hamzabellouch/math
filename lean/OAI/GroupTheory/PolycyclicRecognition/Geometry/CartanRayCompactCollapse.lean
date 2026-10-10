import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryInverseShadow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayActionTopology
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RayCompactCollapse

namespace OAI

/-! # Compact ambient shadows collapse under the actual negative ray -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

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
/-- The actual ambient ray fixes the quotient basepoint and contracts
projected points from every fixed compact ambient set, uniformly for
arbitrary choices of those points. -/
theorem ambient_ray_fixes_one_and_contracts_compact_orbits
    (hExpQ : IsGroupExponential ExpQ) (hπcont : Continuous π)
    (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (v : H) (hv : α₀ v < 0) :
    let ray := fun n : ℕ => ExpG (((n : ℝ) • v : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (∀ n, act (ray n) 1 = 1) ∧ ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => act (ray n) (act (k n) 1)) atTop (𝓝 1) := by
  let ray := fun n : ℕ => ExpG (((n : ℝ) • v : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  let d := fun n : ℕ => F.ExpD (F.D.equiv ((n : ℝ) • v))
  have hray (n : ℕ) : ray n = F.inclusionD (d n) := by
    exact (F.compatibleD ((n : ℝ) • v)).symm
  have hactray (n : ℕ) (q : Q.carrier) : act (ray n) q = α (d n) q := by
    exact (congrArg (fun g : G => act g q) (hray n)).trans
      (factor_quotient_action_second F.inclusionN F.inclusionD π α act hact (d n) q)
  refine ⟨?_, ?_⟩
  · intro n
    exact (hactray n 1).trans (map_one (α (d n)))
  · intro K hK k hk
    obtain ⟨C, hC, hcover⟩ := exists_compact_factor_quotient_orbit F π hπcont α act hact hK
    have ht := M.ray_compact_sequence_tendsto_one T α₀ Q ExpQ hExpQ hbijQ chartQ hchartQ
      v hv C hC (fun n => act (k n) 1) (fun n => hcover (k n) (hk n))
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun n => by
      have he := M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
        hbijN hbijD dynkinN π hπ α hα hφ (d n) (act (k n) 1)
      have hlog : cartanLog H F.D.equiv F.ExpD hbijD (d n) = (n : ℝ) • v :=
        cartanLog_exp H F.D.equiv F.ExpD hbijD ((n : ℝ) • v)
      have he' := congrArg (fun h : H => exponentialConjugate Q.equiv ExpQ hbijQ
        (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h)
          (act (k n) 1)) hlog
      exact (he.trans he').symm.trans (hactray n (act (k n) 1)).symm)


end PolycyclicRecognition.CartanWordModel

end

end OAI
