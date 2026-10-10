import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by600_602 : By passesAt 600 602 := by
  apply byRun passesAt 600 2 602
  · rfl
  decide +kernel
lemma by602_605 : By passesAt 602 605 := by
  apply byRun passesAt 602 3 605
  · rfl
  decide +kernel
lemma by600_605 : By passesAt 600 605 := byJoin by600_602 by602_605
lemma by605_607 : By passesAt 605 607 := by
  apply byRun passesAt 605 2 607
  · rfl
  decide +kernel
lemma by607_610 : By passesAt 607 610 := by
  apply byRun passesAt 607 3 610
  · rfl
  decide +kernel
lemma by605_610 : By passesAt 605 610 := byJoin by605_607 by607_610
lemma by600_610 : By passesAt 600 610 := byJoin by600_605 by605_610
lemma by610_612 : By passesAt 610 612 := by
  apply byRun passesAt 610 2 612
  · rfl
  decide +kernel
lemma by612_615 : By passesAt 612 615 := by
  apply byRun passesAt 612 3 615
  · rfl
  decide +kernel
lemma by610_615 : By passesAt 610 615 := byJoin by610_612 by612_615
lemma by615_617 : By passesAt 615 617 := by
  apply byRun passesAt 615 2 617
  · rfl
  decide +kernel
lemma by617_620 : By passesAt 617 620 := by
  apply byRun passesAt 617 3 620
  · rfl
  decide +kernel
lemma by615_620 : By passesAt 615 620 := byJoin by615_617 by617_620
lemma by610_620 : By passesAt 610 620 := byJoin by610_615 by615_620
lemma by600_620 : By passesAt 600 620 := byJoin by600_610 by610_620
end GeneralMahler.SCal.Grid.Nodes

end OAI
