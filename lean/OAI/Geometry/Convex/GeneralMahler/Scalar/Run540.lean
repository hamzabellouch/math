import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by540_542 : By passesAt 540 542 := by
  apply byRun passesAt 540 2 542
  · rfl
  decide +kernel
lemma by542_545 : By passesAt 542 545 := by
  apply byRun passesAt 542 3 545
  · rfl
  decide +kernel
lemma by540_545 : By passesAt 540 545 := byJoin by540_542 by542_545
lemma by545_547 : By passesAt 545 547 := by
  apply byRun passesAt 545 2 547
  · rfl
  decide +kernel
lemma by547_550 : By passesAt 547 550 := by
  apply byRun passesAt 547 3 550
  · rfl
  decide +kernel
lemma by545_550 : By passesAt 545 550 := byJoin by545_547 by547_550
lemma by540_550 : By passesAt 540 550 := byJoin by540_545 by545_550
lemma by550_552 : By passesAt 550 552 := by
  apply byRun passesAt 550 2 552
  · rfl
  decide +kernel
lemma by552_555 : By passesAt 552 555 := by
  apply byRun passesAt 552 3 555
  · rfl
  decide +kernel
lemma by550_555 : By passesAt 550 555 := byJoin by550_552 by552_555
lemma by555_557 : By passesAt 555 557 := by
  apply byRun passesAt 555 2 557
  · rfl
  decide +kernel
lemma by557_560 : By passesAt 557 560 := by
  apply byRun passesAt 557 3 560
  · rfl
  decide +kernel
lemma by555_560 : By passesAt 555 560 := byJoin by555_557 by557_560
lemma by550_560 : By passesAt 550 560 := byJoin by550_555 by555_560
lemma by540_560 : By passesAt 540 560 := byJoin by540_550 by550_560
end GeneralMahler.SCal.Grid.Nodes

end OAI
