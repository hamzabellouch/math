import OAI.Dynamics.EntropyCounterexample.CoordinateGoodCover
import OAI.Dynamics.EntropyCounterexample.RawSpectrumFactor
import OAI.Dynamics.EntropyCounterexample.ClockModel
import OAI.Dynamics.EntropyCounterexample.SphereCharts

namespace OAI

noncomputable section

namespace Problem340.CoordinateGoodCover

def rawBaseGoodCover : GoodCover ((Bool × Fin 2) × (Bool × Fin 3)) RawBase :=
  clockSphereGoodCover.comap
    (ClockModel.clockHomeomorph.prodCongr complexSphereHomeomorph)

theorem card_rawBaseGoodCover_index :
    Fintype.card ((Bool × Fin 2) × (Bool × Fin 3)) = 24 := by
  norm_num

end Problem340.CoordinateGoodCover

end

end OAI
