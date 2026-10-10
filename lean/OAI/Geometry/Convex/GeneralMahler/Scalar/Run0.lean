import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by0_2 : By passesAt 0 2 := by
  apply byRun passesAt 0 2 2
  · rfl
  decide +kernel
lemma by2_5 : By passesAt 2 5 := by
  apply byRun passesAt 2 3 5
  · rfl
  decide +kernel
lemma by0_5 : By passesAt 0 5 := byJoin by0_2 by2_5
lemma by5_7 : By passesAt 5 7 := by
  apply byRun passesAt 5 2 7
  · rfl
  decide +kernel
lemma by7_10 : By passesAt 7 10 := by
  apply byRun passesAt 7 3 10
  · rfl
  decide +kernel
lemma by5_10 : By passesAt 5 10 := byJoin by5_7 by7_10
lemma by0_10 : By passesAt 0 10 := byJoin by0_5 by5_10
lemma by10_12 : By passesAt 10 12 := by
  apply byRun passesAt 10 2 12
  · rfl
  decide +kernel
lemma by12_15 : By passesAt 12 15 := by
  apply byRun passesAt 12 3 15
  · rfl
  decide +kernel
lemma by10_15 : By passesAt 10 15 := byJoin by10_12 by12_15
lemma by15_17 : By passesAt 15 17 := by
  apply byRun passesAt 15 2 17
  · rfl
  decide +kernel
lemma by17_20 : By passesAt 17 20 := by
  apply byRun passesAt 17 3 20
  · rfl
  decide +kernel
lemma by15_20 : By passesAt 15 20 := byJoin by15_17 by17_20
lemma by10_20 : By passesAt 10 20 := byJoin by10_15 by15_20
lemma by0_20 : By passesAt 0 20 := byJoin by0_10 by10_20
end GeneralMahler.SCal.Grid.Nodes

end OAI
