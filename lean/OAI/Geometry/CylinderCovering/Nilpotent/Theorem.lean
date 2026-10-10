import OAI.Geometry.CylinderCovering.Nilpotent.Bounds
import OAI.Geometry.CylinderCovering.Nilpotent.Counterexample

namespace OAI

namespace CylinderCovering.Nilpotent

theorem finiteCounterexample : FiniteCounterexampleStatement := by
  obtain ⟨n, C, hC, hcover, harea⟩ := finite_counterexample
  refine ⟨n, C, hC, hcover, ?_⟩
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using harea

theorem fullConstruction : FullConstructionStatement :=
  fullConstruction_of_finite finiteCounterexample

end CylinderCovering.Nilpotent

end OAI
