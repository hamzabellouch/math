import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialInnerAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FilteredNilpotentPerturbation

namespace OAI

/-! # Inner perturbations of unipotent nilpotent-group automorphisms

Inner conjugations act trivially on every lower-central quotient. Consequently
multiplying a unipotent automorphism by an arbitrary inner automorphism is
still unipotent, even when the two automorphisms do not commute.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialInnerLieEquiv (w : L) : L ≃ₗ⁅ℝ⁆ L :=
  polynomialModelLieEquiv (MulAut.conj w) ((contMDiff_conjugation w).of_le (by simp))

@[simp] theorem polynomialInnerLieEquiv_apply (w x : L) :
    polynomialInnerLieEquiv w x = w * x * w⁻¹ :=
  polynomialModelLieEquiv_apply _ _ x

theorem polynomial_inner_sub_mem_succ (w : L) (k : ℕ) (x : L)
    (hx : x ∈ lowerCentralSeries ℝ L L k) :
    polynomialInnerLieEquiv w x - x ∈ lowerCentralSeries ℝ L L (k + 1) := by
  let F : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hw0 : w * (0 : L) = w := by rw [← P.one_eq_zero, mul_one]
  have h1 : (w * x - w) - x ∈ F (k + 1) := by
    simpa only [sub_self, sub_zero, zero_add, hw0] using
      polynomial_mul_difference k w x w 0 (by simp) (by simpa using hx)
  have hd : w * x - w ∈ F k := by
    have hh := (F k).add_mem
      ((antitone_lowerCentralSeries ℝ L L (Nat.le_succ k)) h1) hx
    convert hh using 1; abel
  have h2 : (w * x * w⁻¹ - 0) - (w * x - w) ∈ F (k + 1) := by
    simpa only [sub_self, add_zero, mul_inv_cancel, P.one_eq_zero] using
      polynomial_mul_difference k (w * x) w⁻¹ w w⁻¹ hd (by simp)
  have hh := (F (k + 1)).add_mem h2 h1
  change polynomialInnerLieEquiv w x - x ∈ F (k + 1)
  rw [polynomialInnerLieEquiv_apply]
  convert hh using 1; abel

variable [LieRing.IsNilpotent L]

theorem polynomial_inner_mul_unipotent (U : L ≃ₗ⁅ℝ⁆ L)
    (hU : IsNilpotent (U.toLinearMap - 1)) (w : L) :
    IsNilpotent ((polynomialInnerLieEquiv w).toLinearMap * U.toLinearMap - 1) := by
  let F : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  let a : Module.End ℝ L := (polynomialInnerLieEquiv w).toLinearMap * U.toLinearMap - 1
  let b : Module.End ℝ L := U.toLinearMap - 1
  have hUp (k : ℕ) (x : L) (hx : x ∈ F k) : U x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hIp (k : ℕ) (x : L) (hx : x ∈ F k) : polynomialInnerLieEquiv w x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L L).mp
    (inferInstance : LieModule.IsNilpotent L L)
  apply nilpotent_of_filtered_nilpotent_perturbation F (by simp [F])
    (congrArg LieSubmodule.toSubmodule hc) a b
  · intro k x hx
    exact (F k).sub_mem (hIp k _ (hUp k x hx)) hx
  · intro k x hx
    exact (F k).sub_mem (hUp k x hx) hx
  · intro k x hx
    have hh := polynomial_inner_sub_mem_succ w k (U x) (hUp k x hx)
    change polynomialInnerLieEquiv w (U x) - U x ∈ F (k + 1) at hh
    change (polynomialInnerLieEquiv w (U x) - x) - (U x - x) ∈ F (k + 1)
    convert hh using 1; abel
  · exact hU

end PolycyclicRecognition

end

end OAI
