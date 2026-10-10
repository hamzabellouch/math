import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialKernel

namespace OAI

/-! # Faithfulness from the real triangular exponential

Once a group homomorphism integrating the faithful triangular Lie
representation is constructed, its kernel is trivial. Surjectivity of the
ambient exponential is the only global exponential property used here.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

theorem triangular_representation_injective
    {L G : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]
    {m : ℕ} (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (hj : Function.Injective j)
    (hu : ∀ x, (j x).IsUpperTriangular)
    (Exp : L → G) (hzero : Exp 0 = 1) (hsurj : Function.Surjective Exp)
    (ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (hexp : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) : Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_antisymm _ bot_le
  intro g hg
  change ρ g = 1 at hg
  change g = 1
  obtain ⟨x, rfl⟩ := hsurj g
  have he : NormedSpace.exp (j x) = 1 := by
    have h := congrArg Units.val hg
    simp only [hexp, coe_algebraExpUnit, Units.val_one] at h
    exact h
  have hx : x = 0 := hj (((triangular_exp_eq_one_iff (j x) (hu x)).mp he).trans
    (map_zero j).symm)
  rw [hx, hzero]

end PolycyclicRecognition

end

end OAI
