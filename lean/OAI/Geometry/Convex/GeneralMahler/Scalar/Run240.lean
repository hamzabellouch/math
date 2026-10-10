import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by240_242 : By passesAt 240 242 := by
  apply byRun passesAt 240 2 242
  · rfl
  decide +kernel
lemma by242_245 : By passesAt 242 245 := by
  apply byRun passesAt 242 3 245
  · rfl
  decide +kernel
lemma by240_245 : By passesAt 240 245 := byJoin by240_242 by242_245
lemma by245_247 : By passesAt 245 247 := by
  apply byRun passesAt 245 2 247
  · rfl
  decide +kernel
lemma by247_250 : By passesAt 247 250 := by
  apply byRun passesAt 247 3 250
  · rfl
  decide +kernel
lemma by245_250 : By passesAt 245 250 := byJoin by245_247 by247_250
lemma by240_250 : By passesAt 240 250 := byJoin by240_245 by245_250
lemma by250_252 : By passesAt 250 252 := by
  apply byRun passesAt 250 2 252
  · rfl
  decide +kernel
lemma by252_255 : By passesAt 252 255 := by
  apply byRun passesAt 252 3 255
  · rfl
  decide +kernel
lemma by250_255 : By passesAt 250 255 := byJoin by250_252 by252_255
lemma by255_257 : By passesAt 255 257 := by
  apply byRun passesAt 255 2 257
  · rfl
  decide +kernel
lemma by257_260 : By passesAt 257 260 := by
  apply byRun passesAt 257 3 260
  · rfl
  decide +kernel
lemma by255_260 : By passesAt 255 260 := byJoin by255_257 by257_260
lemma by250_260 : By passesAt 250 260 := byJoin by250_255 by255_260
lemma by240_260 : By passesAt 240 260 := byJoin by240_250 by250_260
end GeneralMahler.SCal.Grid.Nodes

end OAI
