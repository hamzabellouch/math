import OAI.Geometry.CylinderCovering.Rational.CostActual
import OAI.Geometry.CylinderCovering.Rational.Coverage
import OAI.Geometry.CylinderCovering.Rational.Eligibility
import OAI.Geometry.CylinderCovering.Rational.Normalization
import OAI.Geometry.CylinderCovering.Rational.Schedules
import OAI.Geometry.CylinderCovering.Rational.TetrahedronDiameter
import OAI.Geometry.CylinderCovering.Rational.TetrahedronVolume
import OAI.Geometry.CylinderCovering.Rational.ScheduleExpansions

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace SlopeRational

theorem asymptotic_main : AsymptoticStatement := by
  refine ⟨?_, ?_, energyIntegral_tendsto⟩
  · intro d hd q hq
    exact ⟨rationalCoverage_main d q hd hq.1 hq.2.1 hq.2.2,
      weightedCost_expansion hd (hq.1.mono (fun _ h => h.le)) hq.2.1⟩
  · convert ceilingIntegral_tendsto_zero_right using 1

theorem paddingSchedules_main : PaddingSchedulesStatement :=
  paddingSchedules_of_asymptotic referenceTetrahedron_minimumShadowArea asymptotic_main

theorem construction_main : ConstructionStatement :=
  ⟨referenceTetrahedron_minimumShadowArea, asymptotic_main,
    approximationEligibility, paddingSchedules_main⟩

end SlopeRational

end

end OAI
