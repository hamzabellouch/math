import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRescaling
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteCuntzFullness

namespace OAI

section

noncomputable section
namespace Pureness
open TraceCone OrderedSemigroup
open scoped ENNReal CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

def finiteUnitClass : finiteCuntzSubmonoid (A := A) := finitePositiveClass 1 ⟨1,zero_le_one⟩

lemma finiteUnitClass_ne_zero : finiteUnitClass (A := A) ≠ 0 := by
  intro h
  exact one_ne_zero ((finitePositiveClass_eq_zero_iff 1 _).mp h)

theorem finiteState_unit_pos (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    0 < f.1 finiteUnitClass ∧ f.1 finiteUnitClass ≠ ⊤ := by
  refine ⟨?_, finiteCuntz_state_finite hsimple y hy f _⟩
  apply pos_iff_ne_zero.mpr
  intro hz
  obtain ⟨q,hq⟩ := finiteCuntz_nonzero_orderUnit hsimple finiteUnitClass finiteUnitClass_ne_zero y
  have h := f.monotone hq
  rw [f.at_unit, f.at_nsmul, hz, nsmul_zero] at h
  exact not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1) h

theorem finiteState_regularization_pos (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    0 < regularizedFiniteDimension f.toAddHom f.monotone y ∧
      regularizedFiniteDimension f.toAddHom f.monotone y ≤ 1 := by
  let d := regularizedFiniteDimension f.toAddHom f.monotone
  have hu : d finiteUnitClass = f.1 finiteUnitClass :=
    regularizedFiniteDimension_projection f.toAddHom f.monotone 1 ⟨1,zero_le_one⟩ (by simp [IsIdempotentElem])
  refine ⟨?_, ?_⟩
  · apply pos_iff_ne_zero.mpr
    intro hz
    obtain ⟨q,hq⟩ := finiteCuntz_nonzero_orderUnit hsimple y hy finiteUnitClass
    have h := regularizedFiniteDimension_monotone f.toAddHom f.monotone hq
    change d finiteUnitClass ≤ d (q • y) at h
    rw [map_nsmul, hz, nsmul_zero, hu] at h
    exact not_le_of_gt (finiteState_unit_pos hsimple y hy f).1 h
  · exact (regularizedFiniteDimension_le f.toAddHom f.monotone y).trans f.at_unit.le

end Pureness
end
end

end OAI
