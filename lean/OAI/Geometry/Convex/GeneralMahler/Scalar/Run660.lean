import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by660_662 : By passesAt 660 662 := by
  apply byRun passesAt 660 2 662
  · rfl
  decide +kernel
lemma by662_665 : By passesAt 662 665 := by
  apply byRun passesAt 662 3 665
  · rfl
  decide +kernel
lemma by660_665 : By passesAt 660 665 := byJoin by660_662 by662_665
lemma by665_667 : By passesAt 665 667 := by
  apply byRun passesAt 665 2 667
  · rfl
  decide +kernel
lemma by667_670 : By passesAt 667 670 := by
  apply byRun passesAt 667 3 670
  · rfl
  decide +kernel
lemma by665_670 : By passesAt 665 670 := byJoin by665_667 by667_670
lemma by660_670 : By passesAt 660 670 := byJoin by660_665 by665_670
lemma by670_672 : By passesAt 670 672 := by
  apply byRun passesAt 670 2 672
  · rfl
  decide +kernel
lemma by672_675 : By passesAt 672 675 := by
  apply byRun passesAt 672 3 675
  · rfl
  decide +kernel
lemma by670_675 : By passesAt 670 675 := byJoin by670_672 by672_675
lemma by675_677 : By passesAt 675 677 := by
  apply byRun passesAt 675 2 677
  · rfl
  decide +kernel
lemma by677_680 : By passesAt 677 680 := by
  apply byRun passesAt 677 3 680
  · rfl
  decide +kernel
lemma by675_680 : By passesAt 675 680 := byJoin by675_677 by677_680
lemma by670_680 : By passesAt 670 680 := byJoin by670_675 by675_680
lemma by660_680 : By passesAt 660 680 := byJoin by660_670 by670_680
end GeneralMahler.SCal.Grid.Nodes

end OAI
