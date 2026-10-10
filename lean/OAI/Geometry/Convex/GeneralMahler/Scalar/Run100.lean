import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by100_102 : By passesAt 100 102 := by
  apply byRun passesAt 100 2 102
  · rfl
  decide +kernel
lemma by102_105 : By passesAt 102 105 := by
  apply byRun passesAt 102 3 105
  · rfl
  decide +kernel
lemma by100_105 : By passesAt 100 105 := byJoin by100_102 by102_105
lemma by105_107 : By passesAt 105 107 := by
  apply byRun passesAt 105 2 107
  · rfl
  decide +kernel
lemma by107_110 : By passesAt 107 110 := by
  apply byRun passesAt 107 3 110
  · rfl
  decide +kernel
lemma by105_110 : By passesAt 105 110 := byJoin by105_107 by107_110
lemma by100_110 : By passesAt 100 110 := byJoin by100_105 by105_110
lemma by110_112 : By passesAt 110 112 := by
  apply byRun passesAt 110 2 112
  · rfl
  decide +kernel
lemma by112_115 : By passesAt 112 115 := by
  apply byRun passesAt 112 3 115
  · rfl
  decide +kernel
lemma by110_115 : By passesAt 110 115 := byJoin by110_112 by112_115
lemma by115_117 : By passesAt 115 117 := by
  apply byRun passesAt 115 2 117
  · rfl
  decide +kernel
lemma by117_120 : By passesAt 117 120 := by
  apply byRun passesAt 117 3 120
  · rfl
  decide +kernel
lemma by115_120 : By passesAt 115 120 := byJoin by115_117 by117_120
lemma by110_120 : By passesAt 110 120 := byJoin by110_115 by115_120
lemma by100_120 : By passesAt 100 120 := byJoin by100_110 by110_120
end GeneralMahler.SCal.Grid.Nodes

end OAI
