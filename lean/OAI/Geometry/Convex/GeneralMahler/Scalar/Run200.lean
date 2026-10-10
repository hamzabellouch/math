import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by200_202 : By passesAt 200 202 := by
  apply byRun passesAt 200 2 202
  · rfl
  decide +kernel
lemma by202_205 : By passesAt 202 205 := by
  apply byRun passesAt 202 3 205
  · rfl
  decide +kernel
lemma by200_205 : By passesAt 200 205 := byJoin by200_202 by202_205
lemma by205_207 : By passesAt 205 207 := by
  apply byRun passesAt 205 2 207
  · rfl
  decide +kernel
lemma by207_210 : By passesAt 207 210 := by
  apply byRun passesAt 207 3 210
  · rfl
  decide +kernel
lemma by205_210 : By passesAt 205 210 := byJoin by205_207 by207_210
lemma by200_210 : By passesAt 200 210 := byJoin by200_205 by205_210
lemma by210_212 : By passesAt 210 212 := by
  apply byRun passesAt 210 2 212
  · rfl
  decide +kernel
lemma by212_215 : By passesAt 212 215 := by
  apply byRun passesAt 212 3 215
  · rfl
  decide +kernel
lemma by210_215 : By passesAt 210 215 := byJoin by210_212 by212_215
lemma by215_217 : By passesAt 215 217 := by
  apply byRun passesAt 215 2 217
  · rfl
  decide +kernel
lemma by217_220 : By passesAt 217 220 := by
  apply byRun passesAt 217 3 220
  · rfl
  decide +kernel
lemma by215_220 : By passesAt 215 220 := byJoin by215_217 by217_220
lemma by210_220 : By passesAt 210 220 := byJoin by210_215 by215_220
lemma by200_220 : By passesAt 200 220 := byJoin by200_210 by210_220
end GeneralMahler.SCal.Grid.Nodes

end OAI
