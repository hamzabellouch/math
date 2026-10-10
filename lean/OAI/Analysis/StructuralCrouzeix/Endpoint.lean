import OAI.Analysis.StructuralCrouzeix.Main
import OAI.Analysis.StructuralCrouzeix.UnitDisk

namespace OAI

namespace StructuralCrouzeixReference
theorem challenge : StructuralCrouzeix.FullEndpoint ∧
    StructuralCrouzeix.IsAdmissible (Metric.ball (0 : ℂ) 1) :=
  ⟨StructuralCrouzeix.fullEndpoint, StructuralCrouzeix.isAdmissible_unitDisk⟩
end StructuralCrouzeixReference

end OAI
