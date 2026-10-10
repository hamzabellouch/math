import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by560_562 : By passesAt 560 562 := by
  apply byRun passesAt 560 2 562
  · rfl
  decide +kernel
lemma by562_565 : By passesAt 562 565 := by
  apply byRun passesAt 562 3 565
  · rfl
  decide +kernel
lemma by560_565 : By passesAt 560 565 := byJoin by560_562 by562_565
lemma by565_567 : By passesAt 565 567 := by
  apply byRun passesAt 565 2 567
  · rfl
  decide +kernel
lemma by567_570 : By passesAt 567 570 := by
  apply byRun passesAt 567 3 570
  · rfl
  decide +kernel
lemma by565_570 : By passesAt 565 570 := byJoin by565_567 by567_570
lemma by560_570 : By passesAt 560 570 := byJoin by560_565 by565_570
lemma by570_572 : By passesAt 570 572 := by
  apply byRun passesAt 570 2 572
  · rfl
  decide +kernel
lemma by572_575 : By passesAt 572 575 := by
  apply byRun passesAt 572 3 575
  · rfl
  decide +kernel
lemma by570_575 : By passesAt 570 575 := byJoin by570_572 by572_575
lemma by575_577 : By passesAt 575 577 := by
  apply byRun passesAt 575 2 577
  · rfl
  decide +kernel
lemma by577_580 : By passesAt 577 580 := by
  apply byRun passesAt 577 3 580
  · rfl
  decide +kernel
lemma by575_580 : By passesAt 575 580 := byJoin by575_577 by577_580
lemma by570_580 : By passesAt 570 580 := byJoin by570_575 by575_580
lemma by560_580 : By passesAt 560 580 := byJoin by560_570 by570_580
end GeneralMahler.SCal.Grid.Nodes

end OAI
