import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraGroupTangent
import Mathlib.Algebra.Lie.Solvable

namespace OAI

/-! # The Lie algebra of tangent spans

Bilinearity extends the computed commutator identity from curve derivatives
to their finite linear span. Thus the derived group controls the derived Lie
algebra without a closed-subgroup theorem.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- Commutators of tangent spans lie in the tangent span of the derived group. -/
theorem algebraGroupTangentSpan_commutator {D : Subgroup Aˣ} {X Y : A}
    (hX : X ∈ algebraGroupTangentSpan D) (hY : Y ∈ algebraGroupTangentSpan D) :
    X * Y - Y * X ∈ algebraGroupTangentSpan ⁅D, D⁆ := by
  let N := algebraGroupTangentSpan ⁅D, D⁆
  have hright (x : A) (hx : AlgebraGroupTangentVector D x) :
      ∀ y ∈ algebraGroupTangentSpan D, x * y - y * x ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact commutator_mem_derived_tangentSpan hx hy
    | zero => simp
    | add y z hy hz ihy ihz =>
      simpa only [mul_add, add_mul, add_sub_add_comm] using N.add_mem ihy ihz
    | smul r y hy ih =>
      simpa only [mul_smul_comm, smul_mul_assoc, ← smul_sub] using N.smul_mem r ih
  induction hX using Submodule.span_induction with
  | mem x hx => exact hright x hx Y hY
  | zero => simp
  | add x z hx hz ihx ihz =>
    simpa only [mul_add, add_mul, add_sub_add_comm] using N.add_mem ihx ihz
  | smul r x hx ih =>
    simpa only [mul_smul_comm, smul_mul_assoc, ← smul_sub] using N.smul_mem r ih

/-- The tangent span is a concrete Lie subalgebra of the ambient matrix algebra. -/
def algebraGroupTangentLie (D : Subgroup Aˣ) : LieSubalgebra ℝ A :=
  { algebraGroupTangentSpan D with
    lie_mem' := fun {_x _y} hx hy =>
      algebraGroupTangentSpan_mono (Subgroup.commutator_le_self D)
        (algebraGroupTangentSpan_commutator hx hy) }

end PolycyclicRecognition

end

end OAI
