import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by160_162 : By passesAt 160 162 := by
  apply byRun passesAt 160 2 162
  · rfl
  decide +kernel
lemma by162_165 : By passesAt 162 165 := by
  apply byRun passesAt 162 3 165
  · rfl
  decide +kernel
lemma by160_165 : By passesAt 160 165 := byJoin by160_162 by162_165
lemma by165_167 : By passesAt 165 167 := by
  apply byRun passesAt 165 2 167
  · rfl
  decide +kernel
lemma by167_170 : By passesAt 167 170 := by
  apply byRun passesAt 167 3 170
  · rfl
  decide +kernel
lemma by165_170 : By passesAt 165 170 := byJoin by165_167 by167_170
lemma by160_170 : By passesAt 160 170 := byJoin by160_165 by165_170
lemma by170_172 : By passesAt 170 172 := by
  apply byRun passesAt 170 2 172
  · rfl
  decide +kernel
lemma by172_175 : By passesAt 172 175 := by
  apply byRun passesAt 172 3 175
  · rfl
  decide +kernel
lemma by170_175 : By passesAt 170 175 := byJoin by170_172 by172_175
lemma by175_177 : By passesAt 175 177 := by
  apply byRun passesAt 175 2 177
  · rfl
  decide +kernel
lemma by177_180 : By passesAt 177 180 := by
  apply byRun passesAt 177 3 180
  · rfl
  decide +kernel
lemma by175_180 : By passesAt 175 180 := byJoin by175_177 by177_180
lemma by170_180 : By passesAt 170 180 := byJoin by170_175 by175_180
lemma by160_180 : By passesAt 160 180 := byJoin by160_170 by170_180
end GeneralMahler.SCal.Grid.Nodes

end OAI
