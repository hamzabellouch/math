import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayFactorContraction

namespace OAI

/-! # Generator flows invisible in a boundary ray quotient -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- A generator outside the retained ray acts trivially on the actual
quotient, for every real flow parameter. -/
theorem outside_generator_boundary_action_eq_one
    (α₀ : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α₀)))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (π : F.N.carrier →* Q.carrier)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay α₀) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α₀)
    (t : ℝ) : act (ExpG (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 := by
  have hmem : M.letter i ∈ M.coneWordIdeal (positiveWeightRay α₀) :=
    eval_mixed_mem_span M.letter (fun j => (M.weight j : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay α₀)
      (w := FreeMagma.of i) hi
  have hz : M.coneProjection (positiveWeightRay α₀) (t • M.letter i) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ((M.coneWordIdeal _).smul_mem t hmem)
  have hproject : π (F.ExpN (F.N.equiv (t • M.letter i))) = 1 := by
    rw [hπ, hz, map_zero]
    exact hExpQ.map_zero
  apply Equiv.ext
  intro q
  change act (ExpG (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) q = q
  have he := hact (F.ExpN (F.N.equiv (t • M.letter i))) 1 q
  simpa only [map_one, mul_one, one_mul, hproject, F.compatibleN, MulAut.one_apply, LieSubmodule.coe_smul] using he

end PolycyclicRecognition.CartanWordModel

end

end OAI
