import OAI.GroupTheory.PolycyclicRecognition.Geometry.RayTangentContraction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MetricCartanFactorBounds

namespace OAI

/-! # Compact increments and contraction for the actual Cartan factors -/

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

/-- Compact ambient increments have compact quotient images. This uses
compact lifts of the actual factors, so no continuity of an arbitrarily
chosen factorization or permutation-valued action is assumed. -/
theorem exists_compact_factor_quotient_orbit
    {Q : Type*} [Group Q] [TopologicalSpace Q]
    (π : F.N.carrier →* Q) (hπ : Continuous π)
    (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    {K : Set G} (hK : IsCompact K) :
    ∃ C : Set Q, IsCompact C ∧ ∀ g ∈ K, act g 1 ∈ C := by
  obtain ⟨B, hB, hcover⟩ := F.compactLifts K hK
  refine ⟨(fun p : F.N.carrier × F.D.carrier => π p.1) '' B,
    hB.image (hπ.comp continuous_fst), ?_⟩
  intro g hg
  obtain ⟨⟨u, d⟩, hp, he⟩ := hcover hg
  refine ⟨(u, d), hp, ?_⟩
  rw [← he, hact, map_one, mul_one]

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

include hπ hα hφ in
/-- The quotient action of each actual Cartan factor is the exponential
of its induced Lie action, with the actual Cartan logarithm. -/
theorem factor_quotient_action_eq_exponential (d : F.D.carrier) (q : Q.carrier) :
    α d q = exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀)
        (cartanLog H F.D.equiv F.ExpD hbijD d)) q := by
  obtain ⟨v, hv⟩ := hbijQ.surjective q
  obtain ⟨w, hw⟩ := Q.equiv.surjective v
  obtain ⟨x, hx⟩ := M.coneProjection_surjective (positiveWeightRay α₀) w
  have hq : ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)) = q :=
    (congrArg ExpQ ((congrArg Q.equiv hx).trans hw)).trans hv
  rw [← hq]
  let h := cartanLog H F.D.equiv F.ExpD hbijD d
  have he : F.action d (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x)) := by
    exact (congrArg (fun a : MulAut F.N.carrier => a (F.ExpN (F.N.equiv x)))
      (hφ d)).trans (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN
        F.isExpN M.bound_zero (cartanIdealAdjointAutomorphism T H h) x)
  calc
    α d (ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x))) =
        α d (π (F.ExpN (F.N.equiv x))) := congrArg (α d) (hπ x).symm
    _ = π (F.action d (F.ExpN (F.N.equiv x))) := hα d _
    _ = π (F.ExpN (F.N.equiv (cartanIdealAdjointAutomorphism T H h x))) := congrArg π he
    _ = ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀)
        (cartanIdealAdjointAutomorphism T H h x))) := hπ _
    _ = _ := by
      have hp := M.coneAdjoint_projection T (positiveWeightRay α₀)
        (positiveWeightRay_add α₀) h x
      exact (congrArg (fun v => ExpQ (Q.equiv v)) hp).symm.trans
        (exponentialConjugate_apply_exp Q.equiv ExpQ hbijQ
          (M.coneAdjointAutomorphism T (positiveWeightRay α₀)
            (positiveWeightRay_add α₀) h) (M.coneProjection (positiveWeightRay α₀) x)).symm

include hbijQ hchartQ hπ hα hφ in
/-- The contraction estimate is expressed directly in a basis of the
actual tangent algebra and in the actual Cartan factor coordinates. -/
theorem exists_ray_factor_compact_contraction :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀))))
        ℝ (GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier)) (p : ℕ) (rate : ℝ),
      0 < rate ∧ ∀ K : Set Q.carrier, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ d : F.D.carrier,
          α₀ (cartanLog H F.D.equiv F.ExpD hbijD d) ≤ 0 → ∀ q ∈ K,
          ‖b.equivFun (chartQ.symm (α d q))‖ ≤
            A * (1 + ‖(finBasis ℝ H).equivFun
              (cartanLog H F.D.equiv F.ExpD hbijD d)‖) ^ p *
              Real.exp (rate * α₀ (cartanLog H F.D.equiv F.ExpD hbijD d)) := by
  exact exists_compact_contraction_pullback
    (cartanLog H F.D.equiv F.ExpD hbijD)
    (fun h => ‖(finBasis ℝ H).equivFun h‖) α₀ chartQ.symm
    (fun h q => exponentialConjugate Q.equiv ExpQ hbijQ
      (M.coneAdjointAutomorphism T (positiveWeightRay α₀) (positiveWeightRay_add α₀) h) q)
    (fun d q => α d q)
    (M.factor_quotient_action_eq_exponential T F α₀ Q ExpQ hbijQ
      hbijN hbijD dynkinN π hπ α hα hφ)
    (M.exists_ray_tangent_compact_contraction T α₀ Q ExpQ hbijQ chartQ hchartQ)

end PolycyclicRecognition.CartanWordModel

end

end OAI
