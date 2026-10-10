import OAI.Analysis.Pureness.Projections.ProjectionDimensionUniqueness
import OAI.Analysis.Pureness.Quasitrace.CentralQuasitraceCompression
import OAI.Analysis.Pureness.Traces.TracialStates

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def ComplexQuasitrace.projectionDimension (T : ComplexQuasitrace D) (hunit : T 1=1) :
    ProjectionDimension D where
  toFun p := (T p).re
  map_zero := by rw [T.map_zero,Complex.zero_re]
  map_one := by rw [hunit,Complex.one_re]
  nonneg p hp := (Complex.nonneg_iff.mp (T.nonneg p hp.nonneg)).1
  add p q hp hq hpq := by
    have hqp : q*p=0 := by
      simpa only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have hc : Commute p q := (commute_iff_eq _ _).mpr (hpq.trans hqp.symm)
    exact congrArg Complex.re (T.map_add_commuting_selfAdjoint
      ⟨p,hp.isSelfAdjoint⟩ ⟨q,hq.isSelfAdjoint⟩ hc)
  polar v _ := congrArg Complex.re (T.polar v)

def TracialState.projectionDimension (τ : TracialState D) : ProjectionDimension D where
  toFun p := (τ.functional p).re
  map_zero := by rw [map_zero,Complex.zero_re]
  map_one := by rw [τ.normalized,Complex.one_re]
  nonneg p hp := (Complex.nonneg_iff.mp (τ.functional.map_nonneg hp.nonneg)).1
  add p q _ _ _ := by rw [map_add,Complex.add_re]
  polar v _ := congrArg Complex.re (τ.tracial (star v) v)

theorem tracialState_eq_quasitrace_on_projections
    (hcomp : ∀ p q : D, IsStarProjection p → IsStarProjection q →
      (∃ v, star v*v=p ∧ IsStarProjection (v*star v) ∧ v*star v ≤ q) ∨
      (∃ v, star v*v=q ∧ IsStarProjection (v*star v) ∧ v*star v ≤ p))
    (τ : TracialState D) (T : ComplexQuasitrace D) (hunit : T 1=1)
    (p : D) (hp : IsStarProjection p) : τ.functional p=T p := by
  apply Complex.ext
  · exact projection_dimension_unique hcomp τ.projectionDimension (T.projectionDimension hunit) p hp
  · have ht := (Complex.nonneg_iff.mp (τ.functional.map_nonneg hp.nonneg)).2
    have hT := (Complex.nonneg_iff.mp (T.nonneg p hp.nonneg)).2
    exact ht.symm.trans hT
end CuntzPureness

end

end OAI
