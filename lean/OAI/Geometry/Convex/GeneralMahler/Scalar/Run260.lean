import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by260_262 : By passesAt 260 262 := by
  apply byRun passesAt 260 2 262
  · rfl
  decide +kernel
lemma by262_265 : By passesAt 262 265 := by
  apply byRun passesAt 262 3 265
  · rfl
  decide +kernel
lemma by260_265 : By passesAt 260 265 := byJoin by260_262 by262_265
lemma by265_267 : By passesAt 265 267 := by
  apply byRun passesAt 265 2 267
  · rfl
  decide +kernel
lemma by267_270 : By passesAt 267 270 := by
  apply byRun passesAt 267 3 270
  · rfl
  decide +kernel
lemma by265_270 : By passesAt 265 270 := byJoin by265_267 by267_270
lemma by260_270 : By passesAt 260 270 := byJoin by260_265 by265_270
lemma by270_272 : By passesAt 270 272 := by
  apply byRun passesAt 270 2 272
  · rfl
  decide +kernel
lemma by272_275 : By passesAt 272 275 := by
  apply byRun passesAt 272 3 275
  · rfl
  decide +kernel
lemma by270_275 : By passesAt 270 275 := byJoin by270_272 by272_275
lemma by275_277 : By passesAt 275 277 := by
  apply byRun passesAt 275 2 277
  · rfl
  decide +kernel
lemma by277_280 : By passesAt 277 280 := by
  apply byRun passesAt 277 3 280
  · rfl
  decide +kernel
lemma by275_280 : By passesAt 275 280 := byJoin by275_277 by277_280
lemma by270_280 : By passesAt 270 280 := byJoin by270_275 by275_280
lemma by260_280 : By passesAt 260 280 := byJoin by260_270 by270_280
end GeneralMahler.SCal.Grid.Nodes

end OAI
