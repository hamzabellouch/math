import Mathlib
import OAI.Analysis.HardSphere.Operators.SemigroupLaplaceCommute

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma killedTransition_eq_formHeat (N : ℕ) (L : Length) (a : ℝ) {t : ℝ} (ht : 0<t) :
    killedTransition N L a t=formHeat N L a t := by
  rcases subsingleton_or_nontrivial (ScalarL2 N L) with h | h
  · exact Subsingleton.elim _ _
  exact semigroup_eq_heat (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t)
    (killedTransition_selfAdjoint N L a)
    (formResolvent N L a) (formResolvent_isPositive N L a)
    (formResolvent_norm_le_one N L a) (killedLaplace_eq_formResolvent (N := N) (L := L) (a := a)) ht

end HardSphere

end

end OAI
