import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by120_122 : By passesAt 120 122 := by
  apply byRun passesAt 120 2 122
  · rfl
  decide +kernel
lemma by122_125 : By passesAt 122 125 := by
  apply byRun passesAt 122 3 125
  · rfl
  decide +kernel
lemma by120_125 : By passesAt 120 125 := byJoin by120_122 by122_125
lemma by125_127 : By passesAt 125 127 := by
  apply byRun passesAt 125 2 127
  · rfl
  decide +kernel
lemma by127_130 : By passesAt 127 130 := by
  apply byRun passesAt 127 3 130
  · rfl
  decide +kernel
lemma by125_130 : By passesAt 125 130 := byJoin by125_127 by127_130
lemma by120_130 : By passesAt 120 130 := byJoin by120_125 by125_130
lemma by130_132 : By passesAt 130 132 := by
  apply byRun passesAt 130 2 132
  · rfl
  decide +kernel
lemma by132_135 : By passesAt 132 135 := by
  apply byRun passesAt 132 3 135
  · rfl
  decide +kernel
lemma by130_135 : By passesAt 130 135 := byJoin by130_132 by132_135
lemma by135_137 : By passesAt 135 137 := by
  apply byRun passesAt 135 2 137
  · rfl
  decide +kernel
lemma by137_140 : By passesAt 137 140 := by
  apply byRun passesAt 137 3 140
  · rfl
  decide +kernel
lemma by135_140 : By passesAt 135 140 := byJoin by135_137 by137_140
lemma by130_140 : By passesAt 130 140 := byJoin by130_135 by135_140
lemma by120_140 : By passesAt 120 140 := byJoin by120_130 by130_140
end GeneralMahler.SCal.Grid.Nodes

end OAI
