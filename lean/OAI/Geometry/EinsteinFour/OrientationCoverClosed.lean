import OAI.Geometry.EinsteinFour.OrientationCoverCompactness
import OAI.Geometry.EinsteinFour.OrientationCoverCharts

namespace OAI

/-! Separation and countability of the compact smooth orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

instance orientationCover_t3Space : T3Space (OrientationCover M) := inferInstance

instance orientationCover_secondCountable : SecondCountableTopology (OrientationCover M) :=
  ChartedSpace.secondCountable_of_sigmaCompact FourSpace (OrientationCover M)

instance orientationCover_nonempty [Nonempty M] : Nonempty (OrientationCover M) := by
  obtain ⟨x⟩ := ‹Nonempty M›
  exact ⟨⟨x, false⟩⟩

end
end PositiveEinsteinFour.Geometry

end OAI
