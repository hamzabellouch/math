import OAI.NumberTheory.JointDickman.PaperMain

namespace OAI

namespace JointDickman

/-- A rational fixed-scale joint law implies the moving joint law and both order densities. -/
theorem main_results_of_rational_fixedScale (h : RationalFixedScaleLaw) :
    JointDickmanLaw ∧ IncreasingOrderLaw ∧ DecreasingOrderLaw := by
  have hj := jointDickmanLaw_of_rational_fixedScale h
  exact ⟨hj, increasingOrderLaw_of_jointDickmanLaw hj, decreasingOrderLaw_of_jointDickmanLaw hj⟩

end JointDickman

end OAI
