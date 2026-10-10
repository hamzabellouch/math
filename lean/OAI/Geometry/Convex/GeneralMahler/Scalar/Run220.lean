import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by220_222 : By passesAt 220 222 := by
  apply byRun passesAt 220 2 222
  · rfl
  decide +kernel
lemma by222_225 : By passesAt 222 225 := by
  apply byRun passesAt 222 3 225
  · rfl
  decide +kernel
lemma by220_225 : By passesAt 220 225 := byJoin by220_222 by222_225
lemma by225_227 : By passesAt 225 227 := by
  apply byRun passesAt 225 2 227
  · rfl
  decide +kernel
lemma by227_230 : By passesAt 227 230 := by
  apply byRun passesAt 227 3 230
  · rfl
  decide +kernel
lemma by225_230 : By passesAt 225 230 := byJoin by225_227 by227_230
lemma by220_230 : By passesAt 220 230 := byJoin by220_225 by225_230
lemma by230_232 : By passesAt 230 232 := by
  apply byRun passesAt 230 2 232
  · rfl
  decide +kernel
lemma by232_235 : By passesAt 232 235 := by
  apply byRun passesAt 232 3 235
  · rfl
  decide +kernel
lemma by230_235 : By passesAt 230 235 := byJoin by230_232 by232_235
lemma by235_237 : By passesAt 235 237 := by
  apply byRun passesAt 235 2 237
  · rfl
  decide +kernel
lemma by237_240 : By passesAt 237 240 := by
  apply byRun passesAt 237 3 240
  · rfl
  decide +kernel
lemma by235_240 : By passesAt 235 240 := byJoin by235_237 by237_240
lemma by230_240 : By passesAt 230 240 := byJoin by230_235 by235_240
lemma by220_240 : By passesAt 220 240 := byJoin by220_230 by230_240
end GeneralMahler.SCal.Grid.Nodes

end OAI
