import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by280_282 : By passesAt 280 282 := by
  apply byRun passesAt 280 2 282
  · rfl
  decide +kernel
lemma by282_285 : By passesAt 282 285 := by
  apply byRun passesAt 282 3 285
  · rfl
  decide +kernel
lemma by280_285 : By passesAt 280 285 := byJoin by280_282 by282_285
lemma by285_287 : By passesAt 285 287 := by
  apply byRun passesAt 285 2 287
  · rfl
  decide +kernel
lemma by287_290 : By passesAt 287 290 := by
  apply byRun passesAt 287 3 290
  · rfl
  decide +kernel
lemma by285_290 : By passesAt 285 290 := byJoin by285_287 by287_290
lemma by280_290 : By passesAt 280 290 := byJoin by280_285 by285_290
lemma by290_292 : By passesAt 290 292 := by
  apply byRun passesAt 290 2 292
  · rfl
  decide +kernel
lemma by292_295 : By passesAt 292 295 := by
  apply byRun passesAt 292 3 295
  · rfl
  decide +kernel
lemma by290_295 : By passesAt 290 295 := byJoin by290_292 by292_295
lemma by295_297 : By passesAt 295 297 := by
  apply byRun passesAt 295 2 297
  · rfl
  decide +kernel
lemma by297_300 : By passesAt 297 300 := by
  apply byRun passesAt 297 3 300
  · rfl
  decide +kernel
lemma by295_300 : By passesAt 295 300 := byJoin by295_297 by297_300
lemma by290_300 : By passesAt 290 300 := byJoin by290_295 by295_300
lemma by280_300 : By passesAt 280 300 := byJoin by280_290 by290_300
end GeneralMahler.SCal.Grid.Nodes

end OAI
