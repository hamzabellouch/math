import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by520_522 : By passesAt 520 522 := by
  apply byRun passesAt 520 2 522
  · rfl
  decide +kernel
lemma by522_525 : By passesAt 522 525 := by
  apply byRun passesAt 522 3 525
  · rfl
  decide +kernel
lemma by520_525 : By passesAt 520 525 := byJoin by520_522 by522_525
lemma by525_527 : By passesAt 525 527 := by
  apply byRun passesAt 525 2 527
  · rfl
  decide +kernel
lemma by527_530 : By passesAt 527 530 := by
  apply byRun passesAt 527 3 530
  · rfl
  decide +kernel
lemma by525_530 : By passesAt 525 530 := byJoin by525_527 by527_530
lemma by520_530 : By passesAt 520 530 := byJoin by520_525 by525_530
lemma by530_532 : By passesAt 530 532 := by
  apply byRun passesAt 530 2 532
  · rfl
  decide +kernel
lemma by532_535 : By passesAt 532 535 := by
  apply byRun passesAt 532 3 535
  · rfl
  decide +kernel
lemma by530_535 : By passesAt 530 535 := byJoin by530_532 by532_535
lemma by535_537 : By passesAt 535 537 := by
  apply byRun passesAt 535 2 537
  · rfl
  decide +kernel
lemma by537_540 : By passesAt 537 540 := by
  apply byRun passesAt 537 3 540
  · rfl
  decide +kernel
lemma by535_540 : By passesAt 535 540 := byJoin by535_537 by537_540
lemma by530_540 : By passesAt 530 540 := byJoin by530_535 by535_540
lemma by520_540 : By passesAt 520 540 := byJoin by520_530 by530_540
end GeneralMahler.SCal.Grid.Nodes

end OAI
