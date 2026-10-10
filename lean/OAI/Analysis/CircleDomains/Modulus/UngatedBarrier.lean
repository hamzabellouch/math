import OAI.Analysis.CircleDomains.Modulus.CompatibleRealBarrier

namespace OAI

/-! Choosing both gate target sets to be the whole sphere forces the
perturbation region to be empty. Thus the controlled norm is the global
norm required for the ungated barrier selection. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleRealBarrier
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : ℕ → PhysicalRealCoordinate d π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}

theorem penalty_eq_empty_of_univ
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ) : R.penalty = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact R.penalty_avoids ⟨x, R.penalty_inside (subset_closure hx)⟩
    (subset_closure hx) (mem_univ _)

theorem controlledSize_of_univ
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ) :
    R.controlledSize = ENNReal.ofReal (Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
      FiniteTransfer.gradientEnergy R.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) +
      countingSquareNorm R.weight := by
  simp only [controlledSize, R.penalty_eq_empty_of_univ, preimage_empty, sdiff_empty]

end CompatibleRealBarrier
end CircleDomainRigidity

end

end OAI
