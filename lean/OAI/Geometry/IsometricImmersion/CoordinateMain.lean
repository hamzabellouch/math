import OAI.Geometry.IsometricImmersion.Assembly.FinalMetric

namespace OAI

noncomputable section
open Set

namespace SmoothLocal.Geometry

theorem mainTarget : MainTarget :=
  ⟨counterexampleMetric,counterexampleMetric_smoothPositive,
    fun _ => counterexampleMetric_no_local_isometric_immersion⟩

end SmoothLocal.Geometry

end

end OAI
