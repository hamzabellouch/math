import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientJacobian
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHaarMultiplier

namespace OAI

/-! # The quotient Lie automorphism and its exponential Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

/-- An automorphism preserving an ideal in both directions induces an
actual Lie equivalence on the quotient. -/
def lieQuotientAutomorphism
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (I : LieIdeal ℝ L) (F : L ≃ₗ⁅ℝ⁆ L) (hF : ∀ x, F x ∈ I ↔ x ∈ I) :
    (L ⧸ I) ≃ₗ⁅ℝ⁆ (L ⧸ I) := by
  let q := I.toSubmodule.mkQ
  let f := I.toSubmodule.mapQ I.toSubmodule F.toLinearEquiv.toLinearMap
    (fun x hx => (hF x).mpr hx)
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨v, rfl⟩ := I.toSubmodule.mkQ_surjective x
    obtain ⟨w, rfl⟩ := I.toSubmodule.mkQ_surjective y
    have hz : q (F (v - w)) = 0 := by
      change q (F v) = q (F w) at hxy
      simpa only [map_sub, sub_eq_zero] using hxy
    have hvw : v - w ∈ I := (hF (v - w)).mp
      ((Submodule.Quotient.mk_eq_zero I.toSubmodule).mp hz)
    apply sub_eq_zero.mp
    change q v - q w = 0
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr hvw
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := I.toSubmodule.mkQ_surjective x
    exact ⟨q (F.symm v), congrArg q (F.apply_symm_apply v)⟩
  refine { LinearEquiv.ofBijective f ⟨hinj, hsurj⟩ with map_lie' := ?_ }
  intro x y
  obtain ⟨v, rfl⟩ := I.toSubmodule.mkQ_surjective x
  obtain ⟨w, rfl⟩ := I.toSubmodule.mkQ_surjective y
  change q (F ⁅v, w⁆) = q ⁅F v, F w⁆
  rw [F.map_lie]

@[simp] theorem lieQuotientAutomorphism_mk
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (I : LieIdeal ℝ L) (F : L ≃ₗ⁅ℝ⁆ L) (hF : ∀ x, F x ∈ I ↔ x ∈ I) (x : L) :
    lieQuotientAutomorphism I F hF (I.toSubmodule.mkQ x) = I.toSubmodule.mkQ (F x) := rfl

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The induced adjoint Lie automorphism on the cone quotient. -/
def coneAdjointAutomorphism (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) ≃ₗ⁅ℝ⁆
      ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) :=
  lieQuotientAutomorphism (M.coneWordIdeal C) (cartanIdealAdjointAutomorphism T H h)
    (M.coneWordIdeal_adjoint_mem_iff T C hadd h)

theorem det_coneAdjointAutomorphism
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det (M.coneAdjointAutomorphism T C hadd h).toLinearEquiv.toLinearMap =
      Real.exp (LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
        (toEnd ℝ H _ h)) :=
  M.det_cone_adjoint_eq_exp_trace T C hadd h

end CartanWordModel
end PolycyclicRecognition

end

end OAI
