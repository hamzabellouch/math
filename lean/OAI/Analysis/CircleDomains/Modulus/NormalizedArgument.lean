import OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic
import OAI.Analysis.CircleDomains.Topology.CirclePathPrefixes
import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace OAI

/-! Circular argument in turns, and continuous argument increments of
paths avoiding a moving point. These use the existing real covering map. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

abbrev AvoidingPathPoint := {p : C(PathTime, ℂ) × ℂ // p ∉ pathHitSet}

def pathArgument (p : AvoidingPathPoint) : C(unitInterval, UnitAddCircle) :=
  ⟨fun t => normalizedArgument (p.val.1 t - p.val.2), by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_normalizedArgument (sub_ne_zero.mpr
      (fun h => p.property ⟨t, h⟩))).comp (f := fun t => p.val.1 t - p.val.2)
        ((p.val.1.continuous.sub continuous_const).continuousAt)⟩

theorem continuous_pathArgument : Continuous pathArgument := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_iff_continuousAt.mpr
  intro p
  have hn : p.1.val.1 p.2 - p.1.val.2 ≠ 0 :=
    sub_ne_zero.mpr (fun h => p.1.property ⟨p.2, h⟩)
  exact (continuousAt_normalizedArgument hn).comp (f := fun q : AvoidingPathPoint × unitInterval =>
    q.1.val.1 q.2 - q.1.val.2)
    (((continuous_eval.comp
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)).sub
      (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))).continuousAt)

def pathArgumentIncrement (p : AvoidingPathPoint) : ℝ := circlePathIncrement (pathArgument p)

theorem continuous_pathArgumentIncrement : Continuous pathArgumentIncrement :=
  continuous_circlePathIncrement.comp continuous_pathArgument

theorem pathArgumentIncrement_projects (p : AvoidingPathPoint) :
    (pathArgumentIncrement p : UnitAddCircle) =
      normalizedArgument (p.val.1 1 - p.val.2) - normalizedArgument (p.val.1 0 - p.val.2) := by
  unfold pathArgumentIncrement circlePathIncrement
  rw [AddCircle.coe_sub, realCirclePathLift_projects, realCirclePathLift_projects]
  rfl

theorem pathArgumentIncrement_integer_of_closed (p : AvoidingPathPoint)
    (hp : p.val.1 1 = p.val.1 0) :
    ∃ n : ℤ, pathArgumentIncrement p = (n : ℝ) := by
  apply circlePathIncrement_integer
  change normalizedArgument (p.val.1 1 - p.val.2) = normalizedArgument (p.val.1 0 - p.val.2)
  rw [hp]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
