import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeIdealInsideAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealStrictWidth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentCoordinateFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanJacobian

namespace OAI

/-! # The ambient nilpotent inner action on the cone ideal

Every ambient adjoint restricts to a nilpotent derivation of the actual
ideal. Its finite exponential is a Lie automorphism with determinant one.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealInnerDerivation (x : cartanRootIdeal H) :
    LieDerivation ℝ (M.coneWordIdeal C) (M.coneWordIdeal C) where
  toLinearMap := toEnd ℝ (cartanRootIdeal H) (M.coneWordIdeal C) x
  leibniz' u v := by
    apply Subtype.ext
    change ⁅x, ⁅(u : cartanRootIdeal H), (v : cartanRootIdeal H)⁆⁆ =
      ⁅(u : cartanRootIdeal H), ⁅x, (v : cartanRootIdeal H)⁆⁆ -
        ⁅(v : cartanRootIdeal H), ⁅x, (u : cartanRootIdeal H)⁆⁆
    rw [leibniz_lie, ← lie_skew (v : cartanRootIdeal H) ⁅x, (u : cartanRootIdeal H)⁆]
    abel

theorem coneIdealInnerDerivation_pow_coe (x : cartanRootIdeal H) (k : ℕ)
    (v : M.coneWordIdeal C) :
    (((M.coneIdealInnerDerivation C x).toLinearMap ^ k) v : cartanRootIdeal H) =
      ((toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) x) ^ k) v := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change ⁅x, (((M.coneIdealInnerDerivation C x).toLinearMap ^ k) v : cartanRootIdeal H)⁆ = _
    rw [hk]
    rfl

theorem coneIdealInnerDerivation_nilpotent (x : cartanRootIdeal H) :
    (M.coneIdealInnerDerivation C x).toLinearMap ^ M.bound = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [M.coneIdealInnerDerivation_pow_coe, Module.End.pow_apply]
  have hv := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) x (v : cartanRootIdeal H) M.bound
  rw [M.bound_zero] at hv
  exact hv

def coneIdealInnerAutomorphism (x : cartanRootIdeal H) :
    M.coneWordIdeal C ≃ₗ⁅ℝ⁆ M.coneWordIdeal C := by
  letI : Module ℚ (M.coneWordIdeal C) := Module.compHom _ (algebraMap ℚ ℝ)
  exact (M.coneIdealInnerDerivation C x).exp
    ⟨M.bound, M.coneIdealInnerDerivation_nilpotent C x⟩

theorem coneIdealInnerAutomorphism_det (x : cartanRootIdeal H) :
    LinearMap.det (M.coneIdealInnerAutomorphism C x).toLinearEquiv.toLinearMap = 1 := by
  let : Module ℚ (M.coneWordIdeal C) := Module.compHom _ (algebraMap ℚ ℝ)
  exact det_nilpotent_exp (M.coneIdealInnerDerivation C x).toLinearMap
    ⟨M.bound, M.coneIdealInnerDerivation_nilpotent C x⟩

theorem coneIdealInnerAutomorphism_apply (x : cartanRootIdeal H)
    (v : M.coneWordIdeal C) :
    M.coneIdealInnerAutomorphism C x v =
      finiteEndFlow (M.coneIdealInnerDerivation C x).toLinearMap M.bound 1 v := by
  let : Module ℚ (M.coneWordIdeal C) := Module.compHom _ (algebraMap ℚ ℝ)
  change IsNilpotent.exp (M.coneIdealInnerDerivation C x).toLinearMap v = _
  rw [IsNilpotent.exp_eq_sum (M.coneIdealInnerDerivation_nilpotent C x)]
  simp only [finiteEndFlow, LinearMap.sum_apply, LinearMap.smul_apply, one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [Rat.cast_inv, Rat.cast_natCast]

theorem coneIdealInnerAutomorphism_letter (i : Fin M.letterCount) (t : ℝ)
    (v : M.coneWordIdeal C) :
    M.coneIdealInnerAutomorphism C (t • M.letter i) v =
      M.coneIdealLetterFlow C i t v := by
  rw [M.coneIdealInnerAutomorphism_apply]
  change finiteEndFlow (toEnd ℝ (cartanRootIdeal H) (M.coneWordIdeal C)
    (t • M.letter i)) M.bound 1 v = _
  rw [map_smul, finiteEndFlow_smul, mul_one]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
