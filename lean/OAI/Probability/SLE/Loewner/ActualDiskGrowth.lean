import OAI.Probability.SLE.Loewner.UnivalentSecondCoefficient
import OAI.Probability.SLE.Geometry.DiskGrowthFromSecondCoefficient

namespace OAI

/-! The sharp disk-growth estimate follows from the odd-root area
estimate and radial integration. -/
noncomputable section

namespace SLEExactGauge

theorem actual_diskUnivalentGrowth : PublishedDiskUnivalentGrowth :=
  diskGrowth_of_secondDerivative (fun _ hf hi => univalent_second_derivative_bound hf hi)

end SLEExactGauge

end

end OAI
