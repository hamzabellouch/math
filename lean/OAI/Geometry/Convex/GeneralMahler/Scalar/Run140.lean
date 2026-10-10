import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by140_142 : By passesAt 140 142 := by
  apply byRun passesAt 140 2 142
  · rfl
  decide +kernel
lemma by142_145 : By passesAt 142 145 := by
  apply byRun passesAt 142 3 145
  · rfl
  decide +kernel
lemma by140_145 : By passesAt 140 145 := byJoin by140_142 by142_145
lemma by145_147 : By passesAt 145 147 := by
  apply byRun passesAt 145 2 147
  · rfl
  decide +kernel
lemma by147_150 : By passesAt 147 150 := by
  apply byRun passesAt 147 3 150
  · rfl
  decide +kernel
lemma by145_150 : By passesAt 145 150 := byJoin by145_147 by147_150
lemma by140_150 : By passesAt 140 150 := byJoin by140_145 by145_150
lemma by150_152 : By passesAt 150 152 := by
  apply byRun passesAt 150 2 152
  · rfl
  decide +kernel
lemma by152_155 : By passesAt 152 155 := by
  apply byRun passesAt 152 3 155
  · rfl
  decide +kernel
lemma by150_155 : By passesAt 150 155 := byJoin by150_152 by152_155
lemma by155_157 : By passesAt 155 157 := by
  apply byRun passesAt 155 2 157
  · rfl
  decide +kernel
lemma by157_160 : By passesAt 157 160 := by
  apply byRun passesAt 157 3 160
  · rfl
  decide +kernel
lemma by155_160 : By passesAt 155 160 := byJoin by155_157 by157_160
lemma by150_160 : By passesAt 150 160 := byJoin by150_155 by155_160
lemma by140_160 : By passesAt 140 160 := byJoin by140_150 by150_160
end GeneralMahler.SCal.Grid.Nodes

end OAI
