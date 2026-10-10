import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by300_302 : By passesAt 300 302 := by
  apply byRun passesAt 300 2 302
  · rfl
  decide +kernel
lemma by302_305 : By passesAt 302 305 := by
  apply byRun passesAt 302 3 305
  · rfl
  decide +kernel
lemma by300_305 : By passesAt 300 305 := byJoin by300_302 by302_305
lemma by305_307 : By passesAt 305 307 := by
  apply byRun passesAt 305 2 307
  · rfl
  decide +kernel
lemma by307_310 : By passesAt 307 310 := by
  apply byRun passesAt 307 3 310
  · rfl
  decide +kernel
lemma by305_310 : By passesAt 305 310 := byJoin by305_307 by307_310
lemma by300_310 : By passesAt 300 310 := byJoin by300_305 by305_310
lemma by310_312 : By passesAt 310 312 := by
  apply byRun passesAt 310 2 312
  · rfl
  decide +kernel
lemma by312_315 : By passesAt 312 315 := by
  apply byRun passesAt 312 3 315
  · rfl
  decide +kernel
lemma by310_315 : By passesAt 310 315 := byJoin by310_312 by312_315
lemma by315_317 : By passesAt 315 317 := by
  apply byRun passesAt 315 2 317
  · rfl
  decide +kernel
lemma by317_320 : By passesAt 317 320 := by
  apply byRun passesAt 317 3 320
  · rfl
  decide +kernel
lemma by315_320 : By passesAt 315 320 := byJoin by315_317 by317_320
lemma by310_320 : By passesAt 310 320 := byJoin by310_315 by315_320
lemma by300_320 : By passesAt 300 320 := byJoin by300_310 by310_320
end GeneralMahler.SCal.Grid.Nodes

end OAI
