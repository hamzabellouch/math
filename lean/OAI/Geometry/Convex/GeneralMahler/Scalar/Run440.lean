import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by440_442 : By passesAt 440 442 := by
  apply byRun passesAt 440 2 442
  · rfl
  decide +kernel
lemma by442_445 : By passesAt 442 445 := by
  apply byRun passesAt 442 3 445
  · rfl
  decide +kernel
lemma by440_445 : By passesAt 440 445 := byJoin by440_442 by442_445
lemma by445_447 : By passesAt 445 447 := by
  apply byRun passesAt 445 2 447
  · rfl
  decide +kernel
lemma by447_450 : By passesAt 447 450 := by
  apply byRun passesAt 447 3 450
  · rfl
  decide +kernel
lemma by445_450 : By passesAt 445 450 := byJoin by445_447 by447_450
lemma by440_450 : By passesAt 440 450 := byJoin by440_445 by445_450
lemma by450_452 : By passesAt 450 452 := by
  apply byRun passesAt 450 2 452
  · rfl
  decide +kernel
lemma by452_455 : By passesAt 452 455 := by
  apply byRun passesAt 452 3 455
  · rfl
  decide +kernel
lemma by450_455 : By passesAt 450 455 := byJoin by450_452 by452_455
lemma by455_457 : By passesAt 455 457 := by
  apply byRun passesAt 455 2 457
  · rfl
  decide +kernel
lemma by457_460 : By passesAt 457 460 := by
  apply byRun passesAt 457 3 460
  · rfl
  decide +kernel
lemma by455_460 : By passesAt 455 460 := byJoin by455_457 by457_460
lemma by450_460 : By passesAt 450 460 := byJoin by450_455 by455_460
lemma by440_460 : By passesAt 440 460 := byJoin by440_450 by450_460
end GeneralMahler.SCal.Grid.Nodes

end OAI
