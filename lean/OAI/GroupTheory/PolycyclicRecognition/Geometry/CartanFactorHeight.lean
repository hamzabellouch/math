import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLifts

namespace OAI

/-! # Canonical height of the constructed Cartan factors

The nilpotent root factor has zero height. The Cartan logarithm records the
height of every lifted prefix exactly, not just up to bounded error.
-/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {W : Type*} [AddCommGroup W] [Module ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = q (heightProjection T.character x))

include hπExp in
/-- The root ideal lies in the canonical height kernel, hence so does its
entire integrated group. -/
theorem inclusionN_height_eq_one
    (hbij : Function.Bijective F.ExpN) (n : F.N.carrier) :
    π (F.inclusionN n) = 1 := by
  obtain ⟨x, rfl⟩ := (hbij.comp F.N.equiv.bijective).surjective n
  change π (F.inclusionN (F.ExpN (F.N.equiv x))) = 1
  rw [F.compatibleN]
  change (π (ExpG x)).toAdd = 0
  rw [hπExp]
  have hz : heightProjection T.character (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T x.property)
  rw [hz, map_zero]

include hπExp in
/-- Cartan logarithmic coordinates recover the actual ambient height. -/
theorem inclusionD_height
    (hbij : Function.Bijective F.ExpD) (d : F.D.carrier) :
    (π (F.inclusionD d)).toAdd = q (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbij d : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  have h := F.compatibleD (cartanLog H F.D.equiv F.ExpD hbij d)
  rw [exp_cartanLog H F.D.equiv F.ExpD hbij d] at h
  rw [h, hπExp]

include hπExp in
/-- A lifted prefix has precisely the same height as its Cartan coordinate. -/
theorem lifted_prefix_height
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (u : ℕ → G) (v : ℕ → F.N.carrier) (w : ℕ → F.D.carrier) (j : ℕ)
    (hlift : F.inclusionN
        (wordPrefix (fun i => (⟨v i, w i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) j).left *
      F.inclusionD (wordPrefix w j) = wordPrefix u j) :
    q (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbijD (wordPrefix w j) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) = (π (wordPrefix u j)).toAdd := by
  rw [← F.inclusionD_height T q π hπExp hbijD, ← hlift, map_mul,
    F.inclusionN_height_eq_one T q π hπExp hbijN, one_mul]

end PolycyclicRecognition.CartanFactorModel

end

end OAI
