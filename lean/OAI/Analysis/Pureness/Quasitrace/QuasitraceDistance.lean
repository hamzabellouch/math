import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricSize
import OAI.Analysis.Pureness.Quasitrace.QuasitraceNormalization
import Mathlib.Topology.MetricSpace.Completion

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
namespace PositiveQuasitrace
variable (T : PositiveQuasitrace D)

def distance (x y : D) : ℝ := T.metricSize (x-y)
lemma distance_nonneg (x y : D) : 0 ≤ T.distance x y := T.metricSize_nonneg _
lemma distance_self (x : D) : T.distance x x = 0 := by simp [distance,T.metricSize_zero]
lemma distance_comm (x y : D) : T.distance x y = T.distance y x := by
  rw [distance,distance,← neg_sub x y,T.metricSize_neg]
lemma distance_star (x y : D) : T.distance (star x) (star y) = T.distance x y := by
  rw [distance,← star_sub,T.metricSize_star]; rfl
lemma distance_eq_zero_iff (hf : ∀ a : Positive D, a.1 ≠ 0 → 0 < T a) (x y : D) :
    T.distance x y = 0 ↔ x = y := by rw [distance,T.metricSize_eq_zero_iff hf,sub_eq_zero]

variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
include hadd
lemma distance_triangle (x y z : D) : T.distance x z ≤ T.distance x y+T.distance y z := by
  simpa only [sub_add_sub_cancel,distance] using hadd (x-y) (y-z)
lemma distance_add (x y x' y' : D) :
    T.distance (x+y) (x'+y') ≤ T.distance x x'+T.distance y y' := by
  simpa only [distance,add_sub_add_comm] using hadd (x-x') (y-y')
lemma distance_mul (x y x' y' : D) :
    T.distance (x*y) (x'*y') ≤ ‖x‖^(2/3:ℝ)*T.distance y y'+
      ‖y'‖^(2/3:ℝ)*T.distance x x' := by
  have he : x*y-x'*y' = x*(y-y')+(x-x')*y' := by noncomm_ring
  change T.metricSize _ ≤ _
  rw [he]
  exact (hadd _ _).trans (add_le_add (T.metricSize_mul_le_left _ _)
    (by simpa only [mul_comm,distance] using T.metricSize_mul_le_right (x-x') y'))

@[instance_reducible] def pseudoMetricSpace : PseudoMetricSpace D where
  dist := T.distance
  dist_self := T.distance_self
  dist_comm := T.distance_comm
  dist_triangle := T.distance_triangle hadd

@[instance_reducible] def faithfulMetricSpace (hf : ∀ a : Positive D, a.1 ≠ 0 → 0 < T a) : MetricSpace D where
  toPseudoMetricSpace := T.pseudoMetricSpace hadd
  eq_of_dist_eq_zero := fun h => (T.distance_eq_zero_iff hf _ _).mp h
end PositiveQuasitrace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
variable (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
variable (hfinite : ∀ x, d x ≠ ⊤)

@[instance_reducible] def finiteSpectralQuasitracePseudoMetric (n : ℕ) : PseudoMetricSpace (FinMatrix A n) :=
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n).pseudoMetricSpace
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite n)

@[instance_reducible] def regularizedStateQuasitraceMetric [Nontrivial A] (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : OrderedSemigroup.StateSpace y)
    (n : ℕ) : MetricSpace (FinMatrix A n) :=
  let d := regularizedFiniteDimension f.toAddHom f.monotone
  let hd := regularizedFiniteDimension_monotone f.toAddHom f.monotone
  let hlsc := regularizedState_dimension_lsc y f
  let hfinite := regularizedState_dimension_finite hsimple y hy f
  (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n).faithfulMetricSpace
    (finiteSpectralPositiveQuasitrace_metricSize_add d hd hlsc hfinite n)
    (regularizedState_positiveQuasitrace_faithful hsimple y hy f n)
end CuntzPureness

end

end OAI
