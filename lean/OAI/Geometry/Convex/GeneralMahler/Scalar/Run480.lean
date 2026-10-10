import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by480_482 : By passesAt 480 482 := by
  apply byRun passesAt 480 2 482
  · rfl
  decide +kernel
lemma by482_485 : By passesAt 482 485 := by
  apply byRun passesAt 482 3 485
  · rfl
  decide +kernel
lemma by480_485 : By passesAt 480 485 := byJoin by480_482 by482_485
lemma by485_487 : By passesAt 485 487 := by
  apply byRun passesAt 485 2 487
  · rfl
  decide +kernel
lemma by487_490 : By passesAt 487 490 := by
  apply byRun passesAt 487 3 490
  · rfl
  decide +kernel
lemma by485_490 : By passesAt 485 490 := byJoin by485_487 by487_490
lemma by480_490 : By passesAt 480 490 := byJoin by480_485 by485_490
lemma by490_492 : By passesAt 490 492 := by
  apply byRun passesAt 490 2 492
  · rfl
  decide +kernel
lemma by492_495 : By passesAt 492 495 := by
  apply byRun passesAt 492 3 495
  · rfl
  decide +kernel
lemma by490_495 : By passesAt 490 495 := byJoin by490_492 by492_495
lemma by495_497 : By passesAt 495 497 := by
  apply byRun passesAt 495 2 497
  · rfl
  decide +kernel
lemma by497_500 : By passesAt 497 500 := by
  apply byRun passesAt 497 3 500
  · rfl
  decide +kernel
lemma by495_500 : By passesAt 495 500 := byJoin by495_497 by497_500
lemma by490_500 : By passesAt 490 500 := byJoin by490_495 by495_500
lemma by480_500 : By passesAt 480 500 := byJoin by480_490 by490_500
end GeneralMahler.SCal.Grid.Nodes

end OAI
