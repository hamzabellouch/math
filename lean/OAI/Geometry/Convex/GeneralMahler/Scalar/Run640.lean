import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by640_642 : By passesAt 640 642 := by
  apply byRun passesAt 640 2 642
  · rfl
  decide +kernel
lemma by642_645 : By passesAt 642 645 := by
  apply byRun passesAt 642 3 645
  · rfl
  decide +kernel
lemma by640_645 : By passesAt 640 645 := byJoin by640_642 by642_645
lemma by645_647 : By passesAt 645 647 := by
  apply byRun passesAt 645 2 647
  · rfl
  decide +kernel
lemma by647_650 : By passesAt 647 650 := by
  apply byRun passesAt 647 3 650
  · rfl
  decide +kernel
lemma by645_650 : By passesAt 645 650 := byJoin by645_647 by647_650
lemma by640_650 : By passesAt 640 650 := byJoin by640_645 by645_650
lemma by650_652 : By passesAt 650 652 := by
  apply byRun passesAt 650 2 652
  · rfl
  decide +kernel
lemma by652_655 : By passesAt 652 655 := by
  apply byRun passesAt 652 3 655
  · rfl
  decide +kernel
lemma by650_655 : By passesAt 650 655 := byJoin by650_652 by652_655
lemma by655_657 : By passesAt 655 657 := by
  apply byRun passesAt 655 2 657
  · rfl
  decide +kernel
lemma by657_660 : By passesAt 657 660 := by
  apply byRun passesAt 657 3 660
  · rfl
  decide +kernel
lemma by655_660 : By passesAt 655 660 := byJoin by655_657 by657_660
lemma by650_660 : By passesAt 650 660 := byJoin by650_655 by655_660
lemma by640_660 : By passesAt 640 660 := byJoin by640_650 by650_660
end GeneralMahler.SCal.Grid.Nodes

end OAI
