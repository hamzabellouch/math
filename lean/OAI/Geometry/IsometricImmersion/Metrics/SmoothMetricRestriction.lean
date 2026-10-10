import OAI.Geometry.IsometricImmersion.Metric

namespace OAI

noncomputable section
namespace SmoothLocal.Geometry

theorem SmoothPositiveOn.mono {g : MetricField} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hVU : V ⊆ U) : SmoothPositiveOn g V :=
  ⟨fun i j => (hg.1 i j).mono hVU,fun p hp => hg.2 p (hVU hp)⟩

end SmoothLocal.Geometry

end

end OAI
