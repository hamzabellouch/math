import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedReductionData
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraFiltration

namespace OAI

/-! # The residual quotient actions commute on lower-central factors

The two orders of quotient lifts differ by inner automorphisms. Intrinsic BCH
commutator estimates make both inner corrections disappear on the next Lie
lower-central quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q] [IsMulCommutative Q]

theorem jointFixed_action_preserves_lowerCentral (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (k : ℕ) (x : jointFixedLieSubalgebra ss)
    (hx : x ∈ lowerCentralSeries ℝ (jointFixedLieSubalgebra ss) (jointFixedLieSubalgebra ss) k) :
    jointFixedGroupAction ss T hT x ∈
      lowerCentralSeries ℝ (jointFixedLieSubalgebra ss) (jointFixedLieSubalgebra ss) k :=
  LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map (f := (jointFixedLieAction ss T hT).toLieHom) hx)

theorem jointFixed_actions_commute_mod_lowerCentral (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (F.factor q r) = F.factor q r)
    (q r : Q) (k : ℕ) (x : jointFixedLieSubalgebra ss)
    (hx : x ∈ lowerCentralSeries ℝ (jointFixedLieSubalgebra ss) (jointFixedLieSubalgebra ss) k) :
    jointFixedLinearAction ss (A q) (fun S hS => hcomm S hS q)
        (jointFixedLinearAction ss (A r) (fun S hS => hcomm S hS r) x) -
      jointFixedLinearAction ss (A r) (fun S hS => hcomm S hS r)
        (jointFixedLinearAction ss (A q) (fun S hS => hcomm S hS q) x) ∈
      lowerCentralSeries ℝ (jointFixedLieSubalgebra ss) (jointFixedLieSubalgebra ss) (k + 1) := by
  let R := jointFixedFactorSystem F A hact ss hcomm hfixed
  let K := jointFixedLieSubalgebra ss
  have hy : R.action (q * r) x ∈ lowerCentralSeries ℝ K K k :=
    jointFixed_action_preserves_lowerCentral ss (A (q * r)) (fun S hS => hcomm S hS _) k x hx
  have hq := polynomialSubalgebra_inner_difference K (R.factor q r) k (R.action (q * r) x) hy
  have hr := polynomialSubalgebra_inner_difference K (R.factor r q) k (R.action (q * r) x) hy
  rw [← R.action_mul_apply] at hq
  rw [show q * r = r * q from mul_comm q r, ← R.action_mul_apply] at hr
  rw [mul_comm r q] at hr
  have hh := (lowerCentralSeries ℝ K K (k + 1)).sub_mem hq hr
  change R.action q (R.action r x) - R.action r (R.action q x) ∈
    (lowerCentralSeries ℝ K K (k + 1)).toSubmodule
  convert hh using 1
  abel

end PolycyclicRecognition

end

end OAI
