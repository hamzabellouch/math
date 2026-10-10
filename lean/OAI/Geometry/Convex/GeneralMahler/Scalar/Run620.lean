import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by620_622 : By passesAt 620 622 := by
  apply byRun passesAt 620 2 622
  · rfl
  decide +kernel
lemma by622_625 : By passesAt 622 625 := by
  apply byRun passesAt 622 3 625
  · rfl
  decide +kernel
lemma by620_625 : By passesAt 620 625 := byJoin by620_622 by622_625
lemma by625_627 : By passesAt 625 627 := by
  apply byRun passesAt 625 2 627
  · rfl
  decide +kernel
lemma by627_630 : By passesAt 627 630 := by
  apply byRun passesAt 627 3 630
  · rfl
  decide +kernel
lemma by625_630 : By passesAt 625 630 := byJoin by625_627 by627_630
lemma by620_630 : By passesAt 620 630 := byJoin by620_625 by625_630
lemma by630_632 : By passesAt 630 632 := by
  apply byRun passesAt 630 2 632
  · rfl
  decide +kernel
lemma by632_635 : By passesAt 632 635 := by
  apply byRun passesAt 632 3 635
  · rfl
  decide +kernel
lemma by630_635 : By passesAt 630 635 := byJoin by630_632 by632_635
lemma by635_637 : By passesAt 635 637 := by
  apply byRun passesAt 635 2 637
  · rfl
  decide +kernel
lemma by637_640 : By passesAt 637 640 := by
  apply byRun passesAt 637 3 640
  · rfl
  decide +kernel
lemma by635_640 : By passesAt 635 640 := byJoin by635_637 by637_640
lemma by630_640 : By passesAt 630 640 := byJoin by630_635 by635_640
lemma by620_640 : By passesAt 620 640 := byJoin by620_630 by630_640
end GeneralMahler.SCal.Grid.Nodes

end OAI
