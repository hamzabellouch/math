import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates14

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinates (i : Fin 909) : ExponentCode :=
  ((#[coordinateChunk0, coordinateChunk1, coordinateChunk2, coordinateChunk3, coordinateChunk4, coordinateChunk5, coordinateChunk6, coordinateChunk7, coordinateChunk8, coordinateChunk9, coordinateChunk10, coordinateChunk11, coordinateChunk12, coordinateChunk13, coordinateChunk14])[i.val / 64]!)[i.val % 64]!

noncomputable def momentVector (H : CMatrix) : Fin 909 → ℝ :=
  fun i => (coordinates i).moment H

end MUB6.Certificate.PairSemantics

end OAI
