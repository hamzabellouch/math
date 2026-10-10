import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by180_182 : By passesAt 180 182 := by
  apply byRun passesAt 180 2 182
  · rfl
  decide +kernel
lemma by182_185 : By passesAt 182 185 := by
  apply byRun passesAt 182 3 185
  · rfl
  decide +kernel
lemma by180_185 : By passesAt 180 185 := byJoin by180_182 by182_185
lemma by185_187 : By passesAt 185 187 := by
  apply byRun passesAt 185 2 187
  · rfl
  decide +kernel
lemma by187_190 : By passesAt 187 190 := by
  apply byRun passesAt 187 3 190
  · rfl
  decide +kernel
lemma by185_190 : By passesAt 185 190 := byJoin by185_187 by187_190
lemma by180_190 : By passesAt 180 190 := byJoin by180_185 by185_190
lemma by190_192 : By passesAt 190 192 := by
  apply byRun passesAt 190 2 192
  · rfl
  decide +kernel
lemma by192_195 : By passesAt 192 195 := by
  apply byRun passesAt 192 3 195
  · rfl
  decide +kernel
lemma by190_195 : By passesAt 190 195 := byJoin by190_192 by192_195
lemma by195_197 : By passesAt 195 197 := by
  apply byRun passesAt 195 2 197
  · rfl
  decide +kernel
lemma by197_200 : By passesAt 197 200 := by
  apply byRun passesAt 197 3 200
  · rfl
  decide +kernel
lemma by195_200 : By passesAt 195 200 := byJoin by195_197 by197_200
lemma by190_200 : By passesAt 190 200 := byJoin by190_195 by195_200
lemma by180_200 : By passesAt 180 200 := byJoin by180_190 by190_200
end GeneralMahler.SCal.Grid.Nodes

end OAI
